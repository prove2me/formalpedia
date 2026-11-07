-- Prove2me | Theorems.Thm_CritWinSpin_theorem_4_4
-- name    : CritWinSpin.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:08.052019+00:00
-- url     : https://prove2.me/theorems/f855076c-57fc-43bf-b5eb-1bffe0df1cbe
-- title:
--   Theorem 4.4, p.17 — a TM2 sampler within $1/m$ of $\pi^\rho_{J,h}$ in $C(N+B+m)^k\exp(CN\delta^{p/(p-1)})$ steps
-- statement:
--   Let $\rho$ be GHS of type $p$. There is one randomized machine and constants $C,k$ such that for every symmetric rational $(J,h)$ of bit length $B$ with $0\preceq J\preceq\tau(1+\delta)I_N$, $\delta\ge0$, and every integer $m\ge5$, the machine on input $((J,h),m)$ has output law within total variation $1/m$ of $\pi^\rho_{J,h}$ and runs in at most
--   $$C(N+B+m)^k\exp\bigl(CN\delta^{p/(p-1)}\bigr)$$
--   steps.
--
--   This is the algorithmic content of the upper bound, Theorem 1.1(i).
--
--   Differences from the source:
--   - reading: an algorithm, on an unnamed machine model → one randomized Mathlib TM2 machine with a worst-case step bound and computed coin count; reason: the paper names no model; poly(·) absorbs polynomial simulations; the algorithm has no unbounded loop
--   - reading: accuracy η ∈ (0, 1/4), time poly(N, B, 1/η) → integer m ≥ 5 in binary, TV ≤ 1/m, time C (N + B + m)^k exp(C N δ^{p/(p−1)}); reason: with m = ⌈1/η⌉ this gives TV ≤ η in the stated time; a rational η as input with time poly(1/η) is false, since a machine could not read η = (10^L + 1)/(5·10^L), with 1/η < 5 and Θ(L) bits
--   - encoding: O_ρ and poly in (2) → ∃ C, k after ρ and before the instance; reason: the paper's convention that hidden constants depend on ρ
--   - reading: the algorithm above, with bound poly·exp(O(K + 1)) in (24) → some machine, with the second form of the bound in (24); reason: the paper leaves the finite-precision implementation to [Bre76, SL25], so it is not a specific program to transcribe; K = N∆_s is an internal quantity of that algorithm and the printed equality bounds it by the second form
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 4.4, p.17, eq. (24); §4.2, pp.16–17

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_CritWinSpin_encInst
import Definitions.Def_CritWinSpin_RandMachine
open QAlgorithms.LocalHamiltonian QuantumPRC IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- **Theorem 4.4, proof of Theorem 1.1(i)** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256
f77584da…, p.17). One randomized `TM2` machine samples within total variation `1/m` of `π^ρ_{J,h}` in at most
`C (N + B + m)^k exp(C N δ^{p/(p−1)})` steps, for every symmetric rational `0 ⪯ J ⪯ τ(1 + δ) I_N`, `δ ≥ 0`.

**Formalization Note.** The paper's "algorithm above" (pp.16–17) leaves its finite-precision implementation
to [Bre76, SL25], so the theorem is stated as the existence of a machine, on the machine layer. The accuracy
input is an integer `m ≥ 5`, standing for `η = 1/m`; a machine reading a rational `η` could not read its
bits within `poly(1/η)` steps. -/
theorem theorem_4_4 (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ (M : RandMachine) (C : ℝ) (k : ℕ),
      ∀ (N : ℕ) (I : Inst N) (m : ℕ) (δ : ℝ),
        I.1.IsSymm → (castM I.1).PosSemidef → 0 ≤ δ →
        ((tau S * (1 + δ)) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM I.1).PosSemidef → 5 ≤ m →
        tvDist (outLaw M (tupleCode [encInst I, encBin m]) (decConfig S N))
            (gibbsOpt S (castM I.1) (castV I.2)) ≤ 1 / (m : ℝ) ∧
        (M.time (tupleCode [encInst I, encBin m]) : ℝ) ≤
          C * ((N : ℝ) + (bitLen I : ℝ) + (m : ℝ)) ^ k *
            Real.exp (C * (N : ℝ) * δ ^ ((p : ℝ) / ((p : ℝ) - 1))) := by sorry

end CritWinSpin
