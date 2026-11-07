-- Prove2me | Theorems.Thm_CritWinSpin_theorem_1_1
-- name    : CritWinSpin.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:25.242188+00:00
-- url     : https://prove2.me/theorems/686896a1-00f5-489a-b8ce-9a56b04eae1f
-- title:
--   Theorem 1.1, pp.2–3 — sampling in time $\mathrm{poly}\cdot\exp(O(N\delta^{p/(p-1)}))$ and CDH-hardness of learning-to-sample at $\tau(1+N^{-d_p+\varepsilon})$
-- statement:
--   Let $\rho$ be a single-site GHS distribution of type $p\ge2$, with $\tau=(\mathrm{Var}_\rho X)^{-1}$ and $d_p=(p-1)/p$.
--
--   **(i) Upper bound.** There is one randomized machine and constants $C,k$ such that for every symmetric rational instance $(J,h)$ of bit length $B$ with $0\preceq J\preceq\tau(1+\delta)I_N$, $\delta\ge0$, and every integer $m\ge5$, on input $((J,h),m)$ its output law is within total variation $\eta=1/m$ of $\pi^\rho_{J,h}$, and it halts in at most
--   $$C(N+B+m)^k\exp\bigl(CN\delta^{p/(p-1)}\bigr)$$
--   steps.
--
--   **(ii) Lower bound.** There is $C_\rho>0$ such that for every $\varepsilon\in(0,d_p)$ and every bilinear group family satisfying CDH, there is a PPT family $\mathcal F_d$ of instances $(J,h)$ with $h=0$ on $N(d)$ sites, $d\le N(d)=\mathrm{poly}(d)$, satisfying for all $d\ge1$
--   $$0\preceq J\preceq\tau(1+N^{-d_p+\varepsilon})I_N,\qquad\max_{1\le i\le N}\Bigl(|h_i|+\sum_{j=1}^N|J_{ij}|\Bigr)\le C_\rho,$$
--   such that for every PPT algorithm $A$ and every $k=\mathrm{poly}(N)$,
--   $$E_{\mathrm{ext}}(A;k)\ge1-\mathrm{negl}(N),\qquad E_{\mathrm{amp}}(A;k)\ge1-\mathrm{negl}(N).$$
--   The family is chosen independently of $k$ and $A$.
--
--   Both bounds have the same exponent $d_p$: the critical window of the spectral threshold $\tau I_N$ has the same polynomial width for parameter-only sampling and for learning-to-sample with $\mathrm{poly}(N)$ samples.
--
--   Differences from the source:
--   - reading: an algorithm, on an unnamed machine model → one randomized Mathlib TM2 machine with a worst-case step bound and computed coin count; reason: the paper names no model; poly(·) absorbs polynomial simulations; the algorithm has no unbounded loop
--   - reading: accuracy η ∈ (0, 1/4), time poly(N, B, 1/η) → integer m ≥ 5 in binary, TV ≤ 1/m, time C (N + B + m)^k exp(C N δ^{p/(p−1)}); reason: with m = ⌈1/η⌉ this gives TV ≤ η in the stated time; a rational η as input with time poly(1/η) is false, since a machine could not read η = (10^L + 1)/(5·10^L), with 1/η < 5 and Θ(L) bits
--   - encoding: O_ρ and poly in (2) → ∃ C, k after ρ and before the instance; reason: the paper's convention that hidden constants depend on ρ
--   - reading: the CDH assumption for a polynomial-time generated bilinear group family → ∀ F : BilinearFamily (exponent representation), CDH F; reason: every prime-order pairing group has this form via a ↦ g^a; see that definition
--   - encoding: a family satisfying (3), and the same lower bound when h = 0 → one family with h = 0 on every instance; reason: h = 0 satisfies (3), so it witnesses both sentences of the theorem
--   - reading: C_ρ in (3), and (3) for the family F_d → ∃ C_ρ after ρ, p and before ε, F; (3) for every d ≥ 1 and every coin string; reason: C_ρ depends only on ρ (§3, p.10); (3) is stated of the family with no asymptotic qualifier
--   - encoding: k = poly(N), N = poly(d), d ≤ N(d) → k, N polynomially bounded functions of d, with k ≥ 1, d ≤ N(d); reason: equivalent since d ≤ N(d) ≤ poly(d); p.9
--   - encoding: 1 − negl(N) → ∀ c, for all large d, 1 − E ≤ N(d)^{−c}; reason: the definition of negl on p.8
--   - encoding: polynomial-time randomized algorithm → the published uniform OWFLocalDesc.PPT, on the one-tape polynomial-time model; reason: polynomial time is model-robust; p.10 quantifies over probabilistic polynomial-time algorithms
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 1.1, pp.2–3, eqs. (2), (3); Definition 2.2, p.9; Assumption 2.3, p.10

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_CritWinSpin_encInst
import Definitions.Def_CritWinSpin_RandMachine
import Definitions.Def_CritWinSpin_BilinearFamily
import Definitions.Def_CritWinSpin_errExt
open QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- **Theorem 1.1, main theorem** (Liu–Zhang–Ren, *The Critical Window for Sampling and Learning-to-Sample in
Spin Systems*, STOC 2027 submission, manuscript sha256 f77584da…, pp.2–3). Let `ρ` be a single-site GHS
distribution of type `p ≥ 2`, `τ = (Var_ρ X)^{−1}`, `d_p = (p − 1)/p`.

(i) One randomized `TM2` machine, on every symmetric rational `0 ⪯ J ⪯ τ(1 + δ) I_N` (`δ ≥ 0`) of bit length
`B` and every integer `m ≥ 5`, samples within total variation `η = 1/m` of `π^ρ_{J,h}` in at most
`C (N + B + m)^k exp(C N δ^{p/(p−1)})` steps, eq. (2).

(ii) There is `C_ρ` such that for every `ε ∈ (0, d_p)` and every bilinear group family with CDH, there is a
PPT family `F_d` of instances with `h = 0` on `N(d)` sites, `d ≤ N(d) = poly(d)`, satisfying (3) for every
`d ≥ 1`, such that for every PPT `A` and polynomial `k`, `E_ext(A; k)` and `E_amp(A; k)` are at least
`1 − negl(N)`.

**Formalization Note.** `η = 1/m`: for `η ∈ (0, 1/4)`, `m = ⌈1/η⌉ ≥ 5` gives error at most `η` in time
`poly(N, B, 1/η)`; the form with a rational `η` as input and time `poly(N, B, 1/η)` is false for any machine,
which could not read the bits of `η`. Clause (ii) is the form with `h = 0`, which also witnesses the
paper's first sentence, since `h = 0` satisfies (3). The family is chosen before `A` and `k` (p.3). -/
theorem theorem_1_1 (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    (∃ (M : RandMachine) (C : ℝ) (k : ℕ),
      ∀ (N : ℕ) (I : Inst N) (m : ℕ) (δ : ℝ),
        I.1.IsSymm → (castM I.1).PosSemidef → 0 ≤ δ →
        ((tau S * (1 + δ)) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM I.1).PosSemidef → 5 ≤ m →
        tvDist (outLaw M (tupleCode [encInst I, encBin m]) (decConfig S N))
            (gibbsOpt S (castM I.1) (castV I.2)) ≤ 1 / (m : ℝ) ∧
        (M.time (tupleCode [encInst I, encBin m]) : ℝ) ≤
          C * ((N : ℝ) + (bitLen I : ℝ) + (m : ℝ)) ^ k *
            Real.exp (C * (N : ℝ) * δ ^ ((p : ℝ) / ((p : ℝ) - 1)))) ∧
    (∃ Cρ : ℝ, 0 < Cρ ∧ ∀ ε : ℝ, 0 < ε → ε < dExp p → ∀ F : BilinearFamily, CDH F →
      ∃ (Fam : PPT) (Nf : ℕ → ℕ),
        (∀ d, d ≤ Nf d) ∧ PolyBounded Nf ∧
        (∀ d, 1 ≤ d → ∀ ω : Fin (Fam.coins.eval (unary d).length) → Bool,
          ∃ I : Inst (Nf d), Fam.alg (tupleCode [List.ofFn ω, unary d]) = encInst I ∧
            I.1.IsSymm ∧ I.2 = 0 ∧ (castM I.1).PosSemidef ∧
            ((tau S * (1 + (Nf d : ℝ) ^ (-dExp p + ε))) •
                (1 : Matrix (Fin (Nf d)) (Fin (Nf d)) ℝ) - castM I.1).PosSemidef ∧
            width (castM I.1) (castV I.2) ≤ Cρ) ∧
        ∀ (A : PPT) (k : ℕ → ℕ), (∀ d, 1 ≤ k d) → PolyBounded k →
          (∀ c : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀,
            1 - errExt S (famLaw Fam (Nf d) d) A (k d) ≤ 1 / (Nf d : ℝ) ^ c) ∧
          (∀ c : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀,
            1 - errAmp S (famLaw Fam (Nf d) d) A (k d) ≤ 1 / (Nf d : ℝ) ^ c)) := by sorry

end CritWinSpin
