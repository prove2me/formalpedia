-- Prove2me | Theorems.Thm_DRMeanVar_Reform_proposition_1
-- name    : DRMeanVar.Reform.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:11.473628+00:00
-- url     : https://prove2.me/theorems/70b75e70-1e27-42fa-a932-97f6dd31d9ef
-- title:
--   Proposition 1, p. 5 — the least mean in the Wasserstein ball
-- statement:
--   Fix $n\ge1$ observed returns, a radius $\delta\ge0$, $1\le q<\infty$, and conjugate exponents $p,q$ with $1/p+1/q=1$. For any portfolio $\varphi$, the minimum expected return over the Wasserstein ball is attained and equals
--   $$\min_{P\in U_\delta(P_n)}E_P(\varphi^TR)=E_{P_n}(\varphi^TR)-\sqrt\delta\,\|\varphi\|_p.$$
--
--   This identifies the robust mean constraint defining the feasible portfolio set.
--
--   **Formalization Note** `IsLeast` records attainment of the paper's minimum. The cost uses the $q$ norm and the penalty uses its conjugate $p$ norm. The assumptions $n\ge1$, $\delta\ge0$ and finite $q$ make the standing conventions of §2.1 explicit.
-- source:
--   Blanchet, Chen & Zhou, Distributionally Robust Mean-Variance Portfolio Selection with Wasserstein Distances, arXiv:1802.04885v1, p. 5, Proposition 1, (5)

import Mathlib
import Definitions.Def_DRMeanVar_Reform_Setting

open MeasureTheory

namespace DRMeanVar.Reform

/-- Proposition 1, p. 5: the least portfolio mean in the Wasserstein ball. -/
theorem proposition_1 {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ))
    (q p : ENNReal) (δ : ℝ) (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ) :
    IsLeast ((fun P => pMean P φ) '' U q δ R)
      (empMean R φ - Real.sqrt δ * ‖WithLp.toLp p φ‖) := by sorry

end DRMeanVar.Reform
