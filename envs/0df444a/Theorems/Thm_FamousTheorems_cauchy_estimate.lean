-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_estimate
-- name    : FamousTheorems.cauchy_estimate
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:52.379627+00:00
-- url     : https://prove2.me/theorems/7a62ab17-e393-4122-b2d1-43dc7f077e6c
-- title:
--   Cauchy's estimate
-- statement:
--   **Cauchy's estimate.** Let $f$ be holomorphic on the open disc $B(c,R)$ and continuous on its closure, with values in a complex normed space, and suppose $\|f(z)\|\le C$ on the circle $|z-c|=R$. Then
--   $$\|f'(c)\|\le\frac CR.$$
--
--   Cauchy's estimate follows from the Cauchy integral formula for the derivative. It is the key step in Liouville's theorem (a bounded entire function is constant), and hence in one proof of the fundamental theorem of algebra, and its higher-order versions bound the Taylor coefficients of holomorphic functions.
--
--   **Formalization note.** Mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`. `DiffContOnCl ℂ f (Metric.ball c R)` means complex differentiable on the open ball and continuous on its closure.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cauchy_estimate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hd : DiffContOnCl ℂ f (Metric.ball c R)) (hC : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ C) : ‖deriv f c‖ ≤ C / R := by sorry

end FamousTheorems
