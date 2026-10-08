-- Prove2me | Theorems.Thm_CorreaThreshold_Nonadaptive_eq_5
-- name    : CorreaThreshold.Nonadaptive.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:39:48.93818+00:00
-- url     : https://prove2.me/theorems/f26685ad-3676-4de2-9a88-50b92863f1ca
-- title:
--   Equation (5), p. 1458 — feasible substitution in the relaxation
-- statement:
--   Let $0\le z_i\le q_i\le1$ and put $\pi_i=2z_i/[2+(e-2)z_i]$. Substituting these probabilities into (4) gives
--
--   $$F(\pi)=\sum_i b_i z_i\frac{2}{2+(e-2)z_i}f_{N\setminus\{i\}}(z).$$
--
--   This value is at most the optimum of (P). The formula identifies the auxiliary factor that the analytic lemmas bound.
--
--   **Formalization Note** As on the page, $z$ is an optimum of the feasible linear problem in (3), with $0\le z_i\le q_i$ and $\sum_i z_i\le1$. All denominators are positive on that box.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1458, (5); https://doi.org/10.1287/moor.2020.1105

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Bernoulli

namespace CorreaThreshold.Nonadaptive

/-- Substitution in (4) yields (5) and a feasible lower bound on (P). -/
theorem eq_5 {n : ℕ} [NeZero n] (q b z : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ q i)
    (hzsum : (∑ i, z i) ≤ 1)
    (hopt : ∀ w : Fin n → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ q i) →
      (∑ i, w i) ≤ 1 → (∑ i, b i * w i) ≤ (∑ i, b i * z i)) :
    objFour b (fun i => 2 * z i / (2 + (Real.exp 1 - 2) * z i)) =
      ∑ i : Fin n, b i * z i * (2 / (2 + (Real.exp 1 - 2) * z i)) *
        fM (Finset.univ.erase i) z ∧
    (∑ i : Fin n, b i * z i * (2 / (2 + (Real.exp 1 - 2) * z i)) *
        fM (Finset.univ.erase i) z) ≤ objP q b := by sorry

end CorreaThreshold.Nonadaptive
