-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_vector_charfun_product_fubini_20261111
-- name    : AvramDividend.Classical.avram_a06_vector_charfun_product_fubini_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:42:47.776725+00:00
-- url     : https://prove2.me/theorems/629dc254-1920-46c4-89a8-e33cd488e91f
-- title:
--   Hilbert-vector characteristic-function Fubini for product probability measures
-- statement:
--   Vector-valued extension of the already Proved real characteristic-function product Fubini theorem. The Euclidean/Hilbert Fourier kernel is complex exponential of i times a real inner product, hence measurable and of norm one, so Mathlib integral_prod applies. This is exactly the reusable step needed for the original A06 random marked-increment joint Fourier mixing.

import Mathlib
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a06_vector_charfun_product_fubini_20261111
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (f : A × B → WithLp 2 (Fin n → ℝ))
    (hf : Measurable f) (t : WithLp 2 (Fin n → ℝ)) :
    MeasureTheory.charFun (Measure.map f (μ.prod ν)) t =
      ∫ a, MeasureTheory.charFun (Measure.map (fun b => f (a,b)) ν) t ∂μ := by sorry
