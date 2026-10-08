-- Prove2me | Theorems.Thm_CondatPD_FB_eq_29
-- name    : CondatPD.FB.eq_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:53.815634+00:00
-- url     : https://prove2.me/theorems/9bb50057-3e1d-4aea-a2ad-a8cfd30ea740
-- title:
--   Equation (29) — the block metric controls the primal component
-- statement:
--   Write $\kappa=(1/\tau-\sigma\|L\|^2)/\beta$ for positive $\beta,\tau,\sigma$. The quadratic form of $P$ satisfies
--   $$\beta\kappa\|x\|^2\le\langle(x,y),P(x,y)\rangle_I\quad\text{for all }(x,y).$$
--
--   The bound compares the primal norm with the block metric in the cocoercivity calculation.
--
--   **Formalization Note** The page states the same inequality for the difference of two points. Every pair $(x,y)$ is such a difference, so the statements are equivalent.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 11, proof of Theorem 3.1, (29)

import Mathlib
import Definitions.Def_CondatPD_FB_Setting

namespace CondatPD.FB

/-- Equation (29), p. 11: the P-quadratic form bounds βκ times the primal norm squared. -/
theorem eq_29 {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (β τ σ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (hσ : 0 < σ) :
    ∀ (x : X) (y : Y), β * ((1 / τ - σ * ‖L‖ ^ 2) / β) * ‖x‖ ^ 2 ≤
      qP τ σ L x y := by sorry

end CondatPD.FB
