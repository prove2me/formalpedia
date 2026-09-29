-- Prove2me | Theorems.Thm_FamousTheorems_gauss_mean_value_holomorphic
-- name    : FamousTheorems.gauss_mean_value_holomorphic
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:29.515273+00:00
-- url     : https://prove2.me/theorems/0c2a8cd2-ba28-4344-ad4a-ac02e01240c8
-- title:
--   Gauss's mean value theorem for holomorphic functions
-- statement:
--   **Gauss's mean value theorem.** Let $f$ be holomorphic on the open disc $|z-c|<R$ and continuous on its closure, with values in a complex Banach space. Then $f(c)$ equals the average of $f$ over the boundary circle:
--   $$f(c)=\frac1{2\pi}\int_0^{2\pi}f(c+Re^{i\theta})\,d\theta.$$
--
--   This follows directly from Cauchy's integral formula. It implies the maximum modulus principle, and its real part gives the mean value property of harmonic functions.
--
--   **Formalization note.** Mathlib's `DiffContOnCl.circleAverage`. `DiffContOnCl ℂ f U` says $f$ is complex differentiable on $U$ and continuous on its closure. `Real.circleAverage f c R` is the average of $f$ over the circle of radius $|R|$ about $c$, so the disc is `Metric.ball c |R|`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `DiffContOnCl.circleAverage`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gauss_mean_value_holomorphic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : DiffContOnCl ℂ f (Metric.ball c |R|)) :
    Real.circleAverage f c R = f c := by sorry

end FamousTheorems
