-- Prove2me | Theorems.Thm_BoydADMM_Consensus_nonneg_prox_positive_part
-- name    : BoydADMM.Consensus.nonneg_prox_positive_part
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:06:44.273744+00:00
-- url     : https://prove2.me/theorems/7bd4a4aa-554c-4810-99e4-69448188e9c2
-- title:
--   §7.1.1: for $g$ the indicator of $\mathbb R^n_+$ the proximal step is the positive part
-- statement:
--   Let $N\ge1$, $\rho>0$, and let $g$ be the indicator function of the nonnegative orthant $\mathbb R^n_+$ (zero on $\mathbb R^n_+$, $+\infty$ elsewhere). With $v=\bar x^{k+1}+(1/\rho)\bar y^k$, the proximal step
--   $$\operatorname*{minimize}_{z\in\mathbb R^n}\ g(z)+(N\rho/2)\,\|z-v\|_2^2$$
--   has the unique solution $z=v_+$, that is,
--   $$z_j=\max(v_j,0),\qquad j=1,\dots,n.$$
--
--   **Formalization Note** The indicator is encoded by its domain $\{z: z_j\ge0\ \forall j\}$ with value $0$ there. The book prints $(\bar x^{k+1}-(1/\rho)\bar y^k)_+$; the intended reading, forced by the proximal form of the $z$-update displayed earlier on the same page, is $\bar x^{k+1}+(1/\rho)\bar y^k$, which is what is stated.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 52, §7.1.1 (example g = indicator of R^n_+; the book prints x̄^{k+1} − (1/ρ)ȳ^k, corrected to +)

import Mathlib
import Definitions.Def_BoydADMM_Consensus_Model

open scoped BigOperators InnerProductSpace

namespace BoydADMM.Consensus

/-- §7.1.1, p. 52 (sign corrected): for `g` the indicator function of `ℝⁿ₊` (effective domain
`{z | z ≥ 0}`, value `0` there), the proximal step
`argmin_z (g(z) + (Nρ/2)‖z − x̄^{k+1} − (1/ρ)ȳ^k‖²)` has the unique solution
`z = (x̄^{k+1} + (1/ρ)ȳ^k)₊`, componentwise. The book prints `x̄^{k+1} − (1/ρ)ȳ^k`. -/
theorem nonneg_prox_positive_part {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (x y : Fin N → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :
    ((∀ j, 0 ≤ z j) ∧ ∀ z' : EuclideanSpace ℝ (Fin n), (∀ j, 0 ≤ z' j) →
        ((N : ℝ) * ρ / 2) * ‖z - avg x - (1 / ρ) • avg y‖ ^ 2 ≤
          ((N : ℝ) * ρ / 2) * ‖z' - avg x - (1 / ρ) • avg y‖ ^ 2) ↔
      ∀ j, z j = max ((avg x + (1 / ρ) • avg y) j) 0 := by sorry

end BoydADMM.Consensus
