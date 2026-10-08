-- Prove2me | Theorems.Thm_CondatPD_FB_P_strictly_positive
-- name    : CondatPD.FB.P_strictly_positive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:38.995983+00:00
-- url     : https://prove2.me/theorems/bfd76259-5957-479f-a217-667869b03e63
-- title:
--   Proof of Theorem 3.1 — strict positivity of the block operator P
-- statement:
--   Let $P$ be the block operator in (20), with diagonal blocks $\tau^{-1}I$ and $\sigma^{-1}I$ and off-diagonal blocks $-L^*$ and $-L$. If $\tau,\sigma,\beta>0$ and $1/\tau-\sigma\|L\|^2\ge\beta/2$, then its quadratic form is strictly positive away from zero:
--   $$\langle z,Pz\rangle_I>0\quad(z\ne0).$$
--
--   This gives the Hilbertian block metric used for Algorithm 3.1.
--
--   **Formalization Note** Boundedness and self-adjointness are immediate from the continuous linear map $L$ and its adjoint; this item states the strict positivity claim.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 10, proof of Theorem 3.1 after (20)

import Mathlib
import Definitions.Def_CondatPD_FB_Setting

namespace CondatPD.FB

/-- §4, p. 10 after (20): P is strictly positive. -/
theorem P_strictly_positive {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (β τ σ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (hσ : 0 < σ)
    (hstep : β / 2 ≤ 1 / τ - σ * ‖L‖ ^ 2) :
    ∀ (x : X) (y : Y), x ≠ 0 ∨ y ≠ 0 → 0 < qP τ σ L x y := by sorry

end CondatPD.FB
