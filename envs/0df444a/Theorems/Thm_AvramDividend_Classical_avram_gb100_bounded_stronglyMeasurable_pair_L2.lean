-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb100_bounded_stronglyMeasurable_pair_L2
-- name    : AvramDividend.Classical.avram_gb100_bounded_stronglyMeasurable_pair_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:20:04.111072+00:00
-- url     : https://prove2.me/theorems/63ec7b6e-ac7a-4f69-816f-8b7bb3d9cec9
-- title:
--   Bounded strongly measurable random variables have L2 squares and integrable covariance
-- statement:
--   On a finite measure space, two bounded strongly measurable real random variables have integrable squares and integrable product.
-- source:
--   Necessary analytic factor of gb96, itself on original Gaussian two-mesh route gb94.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gb100_bounded_stronglyMeasurable_pair_L2
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (f g : Ω → ℝ) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) (Bf Bg : ℝ)
    (hBf0 : 0 ≤ Bf) (hBg0 : 0 ≤ Bg)
    (hBf : ∀ ω, |f ω| ≤ Bf)
    (hBg : ∀ ω, |g ω| ≤ Bg) :
    Integrable (fun ω => (f ω) ^ 2) P ∧
    Integrable (fun ω => (g ω) ^ 2) P ∧
    Integrable (fun ω => f ω * g ω) P := by sorry
