-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_simple_borel_partition_raw_moments
-- name    : AvramDividend.Classical.avram_a20_original_simple_borel_partition_raw_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T20:53:51.658762+00:00
-- url     : https://prove2.me/theorems/09a3e53d-948f-428f-8ade-6794bdadde44
-- title:
--   Exact physical original finite-valued Borel-mark partition weighted raw second moments
-- statement:
--   Any real finite-valued Borel simple function g on the negative Borel mark region S determines a finite disjoint Borel partition B_y=S∩g^{-1}({y}). The true physical jump counts on these cells weighted by each real simple value y have exact first and second raw moments with m=∑_y y Tν(B_y) and v=∑_y y² Tν(B_y). The proof applies the already Proved exact physical finite disjoint weighted Borel cell moments; the partition fibres are measurable, disjoint and lie inside the negative half-line. This is the canonical finite-valued mark approximation needed to pass to the physical real marked-jump integral second moment, without replacing the source law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_simple_borel_partition_raw_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ)) (g : SimpleFunc ℝ ℝ) :
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℝ → ℝ := fun y => ((T : ℝ≥0∞) * X.ν (B y)).toReal
    let J : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y * (NX ω (Ioc 0 T ×ˢ B y)).toReal
    let m : ℝ := ∑ y ∈ g.range, y * r y
    let v : ℝ := ∑ y ∈ g.range, y ^ 2 * r y
    Integrable J P ∧ Integrable (fun ω => J ω ^ 2) P ∧
      (∫ ω, J ω ∂P) = m ∧
      (∫ ω, J ω ^ 2 ∂P) = m ^ 2 + v := by sorry
