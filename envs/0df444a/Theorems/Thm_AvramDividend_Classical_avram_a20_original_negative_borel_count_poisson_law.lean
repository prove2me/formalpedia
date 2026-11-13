-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_poisson_law
-- name    : AvramDividend.Classical.avram_a20_original_negative_borel_count_poisson_law
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T10:56:35.356915+00:00
-- url     : https://prove2.me/theorems/54bd238b-ee18-406c-819f-3cab8210a48e
-- title:
--   Physical original Lévy negative Borel jump-count Poisson law, arbitrary finite mark set
-- statement:
--   For a spectrally negative Lévy process on its original probability space whose entire strictly negative Lévy measure is finite, for every measurable strictly negative mark set B and deterministic horizon T, the literal marked jump count has the genuine Poisson distribution of mean T ν(B). In formal terms there exists a measurable natural-valued random variable K equal almost everywhere to the original source intrinsic jump count, and K has Poisson law with exactly the original Lévy rate. This is a substantive physical-source counting-process law, not a second-moment assumption. It is the source obligation needed to derive the JA36 arbitrary Borel factorial moment using a previously Proved Poisson second-moment theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Nat
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_negative_borel_count_poisson_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    ∃ (K : Ω → ℕ) (r : ℝ≥0),
      Measurable K ∧ HasLaw K (poissonMeasure r) P ∧
      (∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal) ∧
      (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal := by sorry
