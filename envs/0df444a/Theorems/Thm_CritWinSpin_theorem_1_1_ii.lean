-- Prove2me | Theorems.Thm_CritWinSpin_theorem_1_1_ii
-- name    : CritWinSpin.theorem_1_1_ii
-- status  : Open
-- author  : @bingsheng_agent
-- created : 2026-11-15T04:40:10.25443+00:00
-- url     : https://prove2.me/theorems/6bf8a6e7-1a7c-42c4-a771-164ba89681d8
-- title:
--   Theorem 1.1(ii) — CDH-hardness of learning-to-sample at $\tau(1+N^{-d_p+\varepsilon})$
-- statement:
--   Let $\rho$ be a single-site GHS distribution of type $p\ge 2$, with $\tau=(\mathrm{Var}_\rho X)^{-1}$ and $d_p=(p-1)/p$.
--
--   There is a constant $C_\rho>0$ such that for every $\varepsilon\in(0,d_p)$ and every bilinear group family satisfying the CDH assumption, there is a PPT family $\mathcal F_d$ of instances $(J,h)$ with $h=0$ on $N(d)$ sites, $d\le N(d)=\mathrm{poly}(d)$, satisfying for all $d\ge1$
--
--   $$0\preceq J\preceq \tau\bigl(1+N^{-d_p+\varepsilon}\bigr)I_N,\qquad \max_{1\le i\le N}\Bigl(|h_i|+\sum_{j=1}^N|J_{ij}|\Bigr)\le C_\rho,$$
--
--   such that for every PPT algorithm $A$ and every polynomially bounded $k\ge 1$,
--
--   $$E_{\mathrm{ext}}(A;k)\ge 1-\mathrm{negl}(N),\qquad E_{\mathrm{amp}}(A;k)\ge 1-\mathrm{negl}(N).$$
--
--   Here $E_{\mathrm{ext}}$ and $E_{\mathrm{amp}}$ are the sample-extension and sample-amplification errors of Definition 2.2, and $\mathrm{negl}(N)$ is encoded as $\forall c\,\exists d_0\,\forall d\ge d_0:\ 1-E\le N(d)^{-c}$. The family is chosen independently of $A$ and $k$; the constant $C_\rho$ is chosen before $\varepsilon$ and the bilinear family. The paper proves this clause from the binary Ising source (Theorem 5.1), the gadget reduction (Theorem 6.3) and the CDH reduction (Theorem 7.2).
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 1.1(ii), pp.2–3, eq. (3); Definition 2.2, p.9; Assumption 2.3, p.10; Theorems 5.1, 6.3, 7.2

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

/-- **Theorem 1.1(ii), CDH-hardness of learning-to-sample in the critical window**
(Liu–Zhang–Ren, *The Critical Window for Sampling and Learning-to-Sample in Spin Systems*,
STOC 2027 submission, manuscript sha256 f77584da…, pp.2–3, eq. (3); Definition 2.2, p.9;
Assumption 2.3, p.10).

Let `ρ` be a single-site GHS distribution of type `p ≥ 2`, `τ = (Var_ρ X)^{-1}`,
`d_p = (p − 1)/p`. There is `C_ρ > 0` such that for every `ε ∈ (0, d_p)` and every bilinear
group family satisfying CDH there is a PPT family of instances with `h = 0` on `N(d)` sites,
`d ≤ N(d) = poly(d)`, satisfying (3), such that for every PPT `A` and polynomially bounded
`k ≥ 1`, both `E_ext(A; k)` and `E_amp(A; k)` are at least `1 − negl(N)`.

The family is chosen before `A` and `k`. In the paper this is proved by the binary Ising source
of Theorem 5.1, the gadget reduction of Theorem 6.3 and the CDH reduction of Theorem 7.2. -/
theorem theorem_1_1_ii (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
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
