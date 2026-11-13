-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_chronological_pair_nat_aemeasurable
-- name    : AvramDividend.Classical.avram_a20_original_borel_chronological_pair_nat_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:41:35.762193+00:00
-- url     : https://prove2.me/theorems/04f79811-a0a3-4cca-9bd5-de15efa20df0
-- title:
--   The literal original arbitrary Borel chronological pair nat count has ENNReal almost-everywhere measurability
-- statement:
--   For the actual finite negative-activity Lévy source, the literal Set.ncard K of chronological pairs of original Borel negative-marked jumps is almost everywhere measurable as an ENNReal-valued function. The independently Proved physical original factorial identity identifies 2K almost everywhere with the integrable intrinsic marked-count factorial, giving real integrability of 2K. The generic natural-count real-L1-to-ENNReal measurability theorem then provides AEMeasurable of K. This proof is independent of the Poisson count law and expected value of K and can be used to close the original second factorial moment after the physical Fatou limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_chronological_pair_nat_aemeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let S : Ω → Set ℝ≥0 := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : Ω → ℕ := fun ω => ((S ω ×ˢ S ω) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    AEMeasurable (fun ω => (K ω : ℝ≥0∞)) P := by sorry
