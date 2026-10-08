-- Prove2me | Theorems.Thm_ApproachRegret_Calibration_display13_l1_duality
-- name    : ApproachRegret.Calibration.display13_l1_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:28:55.394381+00:00
-- url     : https://prove2.me/theorems/0c2d201c-d2ae-4e91-853e-ef7c934e84df
-- title:
--   Display (13) — for $x\notin B_1(\varepsilon/2)$, $\mathrm{dist}_1(x,B_1(\varepsilon/2))=-\varepsilon/2-\min_{\|\theta\|_\infty\le1}\langle -x,\theta\rangle$
-- statement:
--   Let $x\in\mathbb R^n$ and $\varepsilon>0$ with $\|x\|_1>\varepsilon/2$, i.e. $x\notin B_1(\varepsilon/2)$. Then both minima below are attained and
--   $$\mathrm{dist}_1\bigl(x,B_1(\varepsilon/2)\bigr)=\min_{y:\|y\|_1\le\varepsilon/2}\|x-y\|_1=-\frac\varepsilon2+\|x\|_1=-\frac\varepsilon2-\min_{\theta:\|\theta\|_\infty\le1}\langle -x,\theta\rangle .$$
--   Equivalently, the minimum of $\langle -x,\theta\rangle$ over the unit cube $B_\infty(1)$ is $-\|x\|_1$.
--
--   This is the duality between the ℓ₁ and ℓ∞ norms that lets the ℓ₁ distance be written as a linear optimization over the cube $B_\infty(1)$, the decision set of the online learner in the calibration algorithm.
--
--   **Formalization Note** The inner product is the Euclidean one on `EuclideanSpace ℝ (Fin n)`; the cube is $\{\theta:|\theta_i|\le1\ \forall i\}$. Both minima are stated with `IsLeast`.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), The Setup, display (13), p. 42

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game

namespace ApproachRegret.Calibration

/-- Display (13) (p. 42): for `x ∉ B₁(ε/2)`,
`dist₁(x, B₁(ε/2)) = −ε/2 + ‖x‖₁ = −ε/2 − min_{‖θ‖∞ ≤ 1} ⟨−x, θ⟩`, both minima attained. -/
theorem display13_l1_duality {n : ℕ} (x : ApproachRegret.ToOLO.E n) (ε : ℝ) (hε : 0 < ε)
    (hx : ε / 2 < l1norm x) :
    IsLeast ((fun y => l1norm (x - y)) '' l1Ball n (ε / 2)) (-(ε / 2) + l1norm x) ∧
      IsLeast ((fun θ => inner ℝ (-x) θ) '' cube n) (-(l1norm x)) := by sorry

end ApproachRegret.Calibration
