-- Prove2me | Theorems.Thm_BesbesZeevi_Parametric_a19
-- name    : BesbesZeevi.Parametric.a19
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:18:38.047948+00:00
-- url     : https://prove2.me/theorems/c807ef93-da7b-4c0a-b9cd-590cf54b46df
-- title:
--   Equation (A-19) — unconstrained price stability
-- statement:
--   For two admissible parameters $\theta^*,\widehat\theta\in\Theta$, the true revenue rate at the true unconstrained optimizer exceeds that at the optimizer computed from $\widehat\theta$, and their difference obeys
--
--   $$0\le p^u(\theta^*)\lambda(p^u(\theta^*);\theta^*)-p^u(\widehat\theta)\lambda(p^u(\widehat\theta);\theta^*)\le2\overline K_2\overline p\,\|\widehat\theta-\theta^*\|_\infty.$$
--
--   This is the parametric stability bound for the revenue-maximizing price.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 32 (PDF p. 34), Step 2, Eq. (A-19)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm

namespace BesbesZeevi.Parametric

/-- Equation (A-19), p. 32: regret in the unconstrained revenue-rate maximizer. -/
theorem a19 {k : ℕ} (D : Market) (F : Family k D)
    (S : OptimizerSelection D F) :
    ∀ θstar ∈ F.Θ, ∀ θhat ∈ F.Θ,
      0 ≤ S.pu θstar * F.demand (S.pu θstar) θstar -
            S.pu θhat * F.demand (S.pu θhat) θstar ∧
      S.pu θstar * F.demand (S.pu θstar) θstar -
            S.pu θhat * F.demand (S.pu θhat) θstar ≤
        2 * F.K2 * D.pHi * ‖θhat - θstar‖ := by sorry

end BesbesZeevi.Parametric
