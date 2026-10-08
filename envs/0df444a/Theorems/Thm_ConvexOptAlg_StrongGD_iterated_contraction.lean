-- Prove2me | Theorems.Thm_ConvexOptAlg_StrongGD_iterated_contraction
-- name    : ConvexOptAlg.StrongGD.iterated_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:21:57.092982+00:00
-- url     : https://prove2.me/theorems/53973679-917a-482c-a2f5-642e58e63f8c
-- title:
--   Proof of Theorem 3.12, p. 279 — exponential squared-distance contraction
-- statement:
--   Under the hypotheses of the preceding one-step inequality, with $\kappa=\beta/\alpha$, every integer $t\ge0$ satisfies
--   $$\|x_{t+1}-x^*\|^2\le\exp\!\left(-\frac{4t}{\kappa+1}\right)\|x_1-x^*\|^2.$$
--
--   The bound records the cumulative contraction required for Theorem 3.12.
--
--   **Formalization Note** The source prints the one-step and iterated inequalities in a single chain. Lean states the iterated assertion separately; the $t=0$ case is equality.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.12, p. 279, final inequality

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace

namespace ConvexOptAlg.StrongGD

/-- The iterated distance bound in the proof of Theorem 3.12, p. 279. -/
theorem iterated_contraction {n : ℕ} (hn : 0 < n) (f : E n → ℝ)
    (g : E n → E n) (α β : ℝ) (hα : 0 < α)
    (hsm : IsBetaSmooth f g β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (xstar : E n) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → E n) (hrun : IsGDRun g (2 / (α + β)) x) :
    ∀ t : ℕ,
      ‖x (t + 1) - xstar‖ ^ 2 ≤
        Real.exp (-(4 * (t : ℝ) / (β / α + 1))) * ‖x 1 - xstar‖ ^ 2 := by sorry

end ConvexOptAlg.StrongGD
