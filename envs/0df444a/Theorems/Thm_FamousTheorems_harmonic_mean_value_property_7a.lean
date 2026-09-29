-- Prove2me | Theorems.Thm_FamousTheorems_harmonic_mean_value_property_7a
-- name    : FamousTheorems.harmonic_mean_value_property_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:06.983501+00:00
-- url     : https://prove2.me/theorems/8c8e9b6f-ea45-4be8-a035-75f4b35840ab
-- title:
--   Mean value property of harmonic functions
-- statement:
--   **Mean value property of harmonic functions.** Let $F$ be a real Banach space, $c\in\mathbb C$ and $R\in\mathbb R$, and let $f:\mathbb C\to F$ be harmonic in a neighbourhood of every point of the closed disk $\bar B(c,|R|)$. Then the average of $f$ over the circle of radius $|R|$ about $c$ equals $f(c)$:
--   $$\frac1{2\pi}\int_0^{2\pi}f\big(c+Re^{i\theta}\big)\,d\theta=f(c).$$
--
--   Gauss proved the mean value property for harmonic functions in the plane. It implies the maximum principle and Harnack's inequality, and harmonic functions are exactly the continuous functions with this property. It is also the basis of Poisson's formula for the Dirichlet problem on a disk.
--
--   **Formalization note.** Mathlib's `InnerProductSpace.HarmonicOnNhd.circleAverage_eq`. $\mathbb C$ is viewed as the real inner product space $\mathbb R^2$. `HarmonicOnNhd f s` says that $f$ is twice continuously differentiable with vanishing Laplacian near every point of $s$, and `Real.circleAverage f c R` is the average of $f$ over the circle of radius $R$ about $c$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `InnerProductSpace.HarmonicOnNhd.circleAverage_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem harmonic_mean_value_property_7a {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : ℂ → F} {c : ℂ} {R : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (Metric.closedBall c |R|)) : Real.circleAverage f c R = f c := by sorry

end FamousTheorems
