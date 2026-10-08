-- Prove2me | Theorems.Thm_ConvexOptAlg_StrongGD_value_gap
-- name    : ConvexOptAlg.StrongGD.value_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:21:39.746979+00:00
-- url     : https://prove2.me/theorems/350bc246-6a60-4a03-a743-a31aa53483f1
-- title:
--   Proof of Theorem 3.12, p. 279 — value gap is at most β/2 times squared distance
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\beta$-smooth with gradient $g$, let $x^*$ minimize $f$ globally, and let $(x_t)$ be a gradient descent run, with $n\ge1$. For each $t\ge1$,
--   $$f(x_t)-f(x^*)\le\frac\beta2\|x_t-x^*\|^2.$$
--
--   This turns a bound on the iterates' distance from the optimizer into a function-value bound.
--
--   **Formalization Note** The inequality is independent of the run's step size; the run places the page's $x_t$ in the statement. The zero gradient at the minimizer follows from differentiability and global minimality.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.12, p. 279, first display

import Mathlib
import Definitions.Def_ConvexOptAlg_StrongGD_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.StrongGD

/-- The smoothness bound at an unconstrained minimizer, proof of Theorem 3.12, p. 279. -/
theorem value_gap {n : ℕ} (hn : 0 < n) (f : E n → ℝ)
    (g : E n → E n) (β : ℝ) (hsm : IsBetaSmooth f g β)
    (xstar : E n) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → E n) (η : ℝ) (hrun : IsGDRun g η x) :
    ∀ t : ℕ, 1 ≤ t →
      f (x t) - f xstar ≤ (β / 2) * ‖x t - xstar‖ ^ 2 := by sorry

end ConvexOptAlg.StrongGD
