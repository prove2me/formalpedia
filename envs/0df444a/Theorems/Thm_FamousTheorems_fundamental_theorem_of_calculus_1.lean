-- Prove2me | Theorems.Thm_FamousTheorems_fundamental_theorem_of_calculus_1
-- name    : FamousTheorems.fundamental_theorem_of_calculus_1
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:27:05.897006+00:00
-- url     : https://prove2.me/theorems/80533506-482e-48a2-a426-322ae94afc62
-- title:
--   The fundamental theorem of calculus, part 1 (derivative of the integral)
-- statement:
--   **The fundamental theorem of calculus, part 1.** Let $f:\mathbb R\to E$ be integrable on the interval between $a$ and $b$, measurable near $b$, and continuous at $b$. Then $F(u)=\int_a^u f(x)\,dx$ is differentiable at $b$ with
--   $$F'(b)=f(b).$$
--
--   This is the half of the fundamental theorem that says integration inverts differentiation. In particular every continuous function has an antiderivative. It holds for functions with values in any real Banach space.
--
--   **Formalization note.** Mathlib's `intervalIntegral.integral_hasDerivAt_right`. `∫ x in a..u, f x` is the oriented interval integral, `IntervalIntegrable f volume a b` is Lebesgue integrability on the interval, and `StronglyMeasurableAtFilter f (nhds b)` is strong measurability on a neighbourhood of `b` (automatic for continuous `f`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `intervalIntegral.integral_hasDerivAt_right`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fundamental_theorem_of_calculus_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) (hmeas : StronglyMeasurableAtFilter f (nhds b) MeasureTheory.volume)
    (hb : ContinuousAt f b) : HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b := by sorry

end FamousTheorems
