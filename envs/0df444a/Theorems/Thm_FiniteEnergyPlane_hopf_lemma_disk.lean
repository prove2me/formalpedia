-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hopf_lemma_disk
-- name    : FiniteEnergyPlane.hopf_lemma_disk
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T17:34:02.654905+00:00
-- url     : https://prove2.me/theorems/c369882a-5b39-5586-985d-d2108f9a5803
-- title:
--   Hopf boundary point lemma on a disk in the plane
-- statement:
--   Let $c \in \mathbb{C}$, $R > 0$, $D = B(c, R)$ and $\zeta \in \partial D$. Let $f : \mathbb{C} \to \mathbb{R}$ be continuous on $\bar D$, $C^2$ on $D$ with $\Delta f \ge 0$ on $D$, and suppose $f(z) < f(\zeta)$ for all $z \in D$. If $f$ has derivative $f'$ at $\zeta$ within $\bar D$, then $f'(\zeta - c) > 0$: the outward normal derivative of $f$ at $\zeta$ is positive.
--
--   Role: strict positivity of the normal derivative at a boundary maximum of a subharmonic function; with a disk inside the domain tangent at a boundary point it applies to any domain satisfying the interior ball condition there.
--
--   Formalization Note: $\Delta$ is Mathlib's Laplacian on $\mathbb{C}$. The derivative is only assumed to exist within the closed disk (`HasFDerivWithinAt`), so $f$ need not be differentiable from outside $\bar D$.
-- source:
--   L. C. Evans, Partial Differential Equations, 2nd ed., AMS (2010), Section 6.4.2; D. Gilbarg, N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer (2001), Section 3.1; E. Hopf, A remark on linear elliptic differential equations of second order, Proc. AMS 3 (1952), 791-793

import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Complex.Basic

namespace FiniteEnergyPlane

open Laplacian Metric

/-- Hopf's boundary point lemma on a disk in `ℂ`. Let `f : ℂ → ℝ` be continuous on the closed disk
`D̄ = closedBall c R` (`R > 0`), `C²` with `Δf ≥ 0` on the open disk `D`, and let `ζ ∈ ∂D` be a point
with `f < f ζ` on `D`. If `f` has derivative `f'` at `ζ` within `D̄`, then the outward normal
derivative is positive: `f'(ζ - c) > 0`. -/
theorem hopf_lemma_disk {c ζ : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℝ} {f' : ℂ →L[ℝ] ℝ}
    (hcont : ContinuousOn f (closedBall c R)) (hf : ContDiffOn ℝ 2 f (ball c R))
    (hΔ : ∀ z ∈ ball c R, 0 ≤ Δ f z) (hlt : ∀ z ∈ ball c R, f z < f ζ)
    (hζ : ζ ∈ sphere c R) (hd : HasFDerivWithinAt f f' (closedBall c R) ζ) :
    0 < f' (ζ - c) := by
  sorry

end FiniteEnergyPlane
