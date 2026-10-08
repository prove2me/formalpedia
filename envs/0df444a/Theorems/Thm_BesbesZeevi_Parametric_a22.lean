-- Prove2me | Theorems.Thm_BesbesZeevi_Parametric_a22
-- name    : BesbesZeevi.Parametric.a22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:18:49.938029+00:00
-- url     : https://prove2.me/theorems/d24946eb-c5a9-4d2c-8fac-2c69ec5a9fac
-- title:
--   Equation (A-22) — capacity-matching price stability
-- statement:
--   For two admissible parameters $\theta^*,\widehat\theta\in\Theta$, the true revenue rates at their capacity-matching prices differ by at most
--
--   $$\left|p^c(\theta^*)\lambda(p^c(\theta^*);\theta^*)-p^c(\widehat\theta)\lambda(p^c(\widehat\theta);\theta^*)\right|\le2(\overline p+M/\underline K)\overline K_2\,\|\widehat\theta-\theta^*\|_\infty.$$
--
--   This is the companion stability bound for the price selected by demand-capacity matching.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 33 (PDF p. 35), Step 2, Eq. (A-22)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm

namespace BesbesZeevi.Parametric

/-- Equation (A-22), p. 33: revenue-rate difference for the capacity-matching price. -/
theorem a22 {k : ℕ} (D : Market) (F : Family k D)
    (S : OptimizerSelection D F) :
    ∀ θstar ∈ F.Θ, ∀ θhat ∈ F.Θ,
      |S.pc θstar * F.demand (S.pc θstar) θstar -
        S.pc θhat * F.demand (S.pc θhat) θstar| ≤
      2 * (D.pHi + D.M * D.KLo⁻¹) * F.K2 * ‖θhat - θstar‖ := by sorry

end BesbesZeevi.Parametric
