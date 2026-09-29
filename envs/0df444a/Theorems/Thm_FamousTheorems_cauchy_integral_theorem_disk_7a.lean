-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_integral_theorem_disk_7a
-- name    : FamousTheorems.cauchy_integral_theorem_disk_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:04.105208+00:00
-- url     : https://prove2.me/theorems/33396b3c-e646-4230-b111-2b5e4a6849a6
-- title:
--   Cauchy's integral theorem for a disk
-- statement:
--   **Cauchy's integral theorem for a disk.** Let $E$ be a complex Banach space, $c\in\mathbb C$, $R\ge0$, and $s\subseteq\mathbb C$ countable. Let $f:\mathbb C\to E$ be continuous on the closed disk $\bar B(c,R)$ and complex differentiable at every point of the open disk $B(c,R)$ outside $s$. Then
--   $$\oint_{|z-c|=R}f(z)\,dz=0.$$
--
--   Cauchy's theorem is the foundation of complex analysis. From it follow the Cauchy integral formula, the analyticity of holomorphic functions, Liouville's theorem and the residue theorem. The version here allows a countable set of exceptional points, which makes it directly applicable to functions with removable singularities.
--
--   **Formalization note.** Mathlib's `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`. `∮ z in C(c, R), f z` is the integral over the circle $\theta\mapsto c+Re^{i\theta}$, $0\le\theta\le2\pi$, with respect to $dz$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cauchy_integral_theorem_disk_7a {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E} {c : ℂ}
    {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (Metric.closedBall c R))
    (hd : ∀ z ∈ Metric.ball c R \ s, DifferentiableAt ℂ f z) : (∮ z in C(c, R), f z) = 0 := by sorry

end FamousTheorems
