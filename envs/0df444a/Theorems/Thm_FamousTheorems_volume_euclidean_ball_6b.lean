-- Prove2me | Theorems.Thm_FamousTheorems_volume_euclidean_ball_6b
-- name    : FamousTheorems.volume_euclidean_ball_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:36.711833+00:00
-- url     : https://prove2.me/theorems/0ea37afc-2473-4822-9426-caff33f6bb9b
-- title:
--   The volume of the n-dimensional Euclidean ball
-- statement:
--   **The volume of the $n$-dimensional Euclidean ball.** Let $E$ be a Euclidean space of dimension $n\ge1$ with its Lebesgue measure. For every centre $x$ and radius $r$,
--   $$\operatorname{vol}\big(B(x,r)\big)=r^n\,\frac{\pi^{n/2}}{\Gamma\!\left(\frac n2+1\right)}.$$
--
--   This formula gives the familiar $2r$, $\pi r^2$ and $\frac43\pi r^3$ in dimensions $1,2,3$. It also shows that the volume of the unit ball tends to $0$ as $n\to\infty$. It is used in the geometry of numbers, in the asymptotics of lattice point counts and sphere packings, and in computing surface areas of spheres.
--
--   **Formalization note.** Mathlib's `InnerProductSpace.volume_ball`. The measure `MeasureTheory.volume` on a finite-dimensional real inner product space is the one that gives an orthonormal parallelepiped volume $1$. The value is written as `ENNReal.ofReal r ^ n * ENNReal.ofReal (√π ^ n / Γ(n/2 + 1))`, where `ENNReal.ofReal r` is $0$ for negative $r$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `InnerProductSpace.volume_ball`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem volume_euclidean_ball_6b {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (x : E) (r : ℝ) :
    MeasureTheory.volume (Metric.ball x r) =
      ENNReal.ofReal r ^ Module.finrank ℝ E *
        ENNReal.ofReal (Real.sqrt Real.pi ^ Module.finrank ℝ E / Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1)) := by sorry

end FamousTheorems
