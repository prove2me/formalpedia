-- Prove2me | Theorems.Thm_BesbesZeevi_Parametric_a23
-- name    : BesbesZeevi.Parametric.a23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:18:45.868263+00:00
-- url     : https://prove2.me/theorems/2c7b786f-96af-491f-a6fa-3f3753353010
-- title:
--   Equation (A-23) — chosen-price stability
-- statement:
--   Write $p^D(\theta)=\max\{p^u(\theta),p^c(\theta)\}$. For admissible $\theta^*$ and $\widehat\theta$, the true revenue-rate loss from using the price computed at $\widehat\theta$ satisfies
--
--   $$p^D(\theta^*)\lambda(p^D(\theta^*);\theta^*)-p^D(\widehat\theta)\lambda(p^D(\widehat\theta);\theta^*)\le C_1\|\widehat\theta-\theta^*\|_\infty,$$
--
--   where $C_1=2(\overline p+M/\underline K)\overline K_2+2\overline K_2\overline p$. This is the deterministic error bound for the price used after learning.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 34 (PDF p. 36), Step 2, Eq. (A-23)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm

namespace BesbesZeevi.Parametric

/-- Equation (A-23), p. 34, with the paper's explicit constant C₁. -/
theorem a23 {k : ℕ} (D : Market) (F : Family k D)
    (S : OptimizerSelection D F) :
    ∀ θstar ∈ F.Θ, ∀ θhat ∈ F.Θ,
      pD S θstar * F.demand (pD S θstar) θstar -
        pD S θhat * F.demand (pD S θhat) θstar ≤
      (2 * (D.pHi + D.M * D.KLo⁻¹) * F.K2 + 2 * F.K2 * D.pHi) *
        ‖θhat - θstar‖ := by sorry

end BesbesZeevi.Parametric
