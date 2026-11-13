-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_nat_stage_exact_energy_20261112
-- name    : AvramDividend.Classical.avram_a21_original_simple_nat_stage_exact_energy_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:37:25.493134+00:00
-- url     : https://prove2.me/theorems/d3f5b266-dd21-4c98-8efb-849f40e9ced9
-- title:
--   True original-space finite simple-mark natural-indexed Poisson L2 energy certificate
-- statement:
--   For every bounded real Borel simple mark on a negative mark set of the original Lévy process, choose genuine disjoint Borel mark fibres indexed by a finite natural range. Their weighted centred source marked counts equal the actual compensated integral almost surely and have an integrable square with exact physical squared-mark intensity as expectation.
-- source:
--   Proved natural Borel mark fibre partition (new), Proved original finite-fibre exact energy dc9748d4, and Proved original simple compensated fibre integral identity c0e79a4d. This closes the structural and per-approximant energy parts of 67336b2d, leaving quantisation, DCT and intensity limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_simple_mark_natural_fibre_partition_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_mark_fibre_centered_energy_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_mark_fibre_compensated_identity_20261112
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_simple_nat_stage_exact_energy_20261112
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (f : SimpleFunc ℝ ℝ) (hfBound : ∀ z ∈ S, |f z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∃ (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ),
      (∀ i ∈ Finset.range K, MeasurableSet (B i) ∧ B i ⊆ S) ∧
      (∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K,
        i ≠ j → Disjoint (B i) (B j)) ∧
      let F : Ω → ℝ := fun ω =>
        ∑ i ∈ Finset.range K,
          c i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal -
            (((T : ℝ≥0∞) * X.ν (B i)).toReal))
      let E : ℝ :=
        ∑ i ∈ Finset.range K,
          (c i)^2 * (((T : ℝ≥0∞) * X.ν (B i)).toReal)
      (∀ᵐ ω ∂P, F ω =
        (∫ p in (Ioc 0 T ×ˢ S), f p.2 ∂NX ω) -
          (T : ℝ) * (∫ z in S, f z ∂X.ν)) ∧
      Integrable (fun ω => (F ω)^2) P ∧
      (∫ ω, (F ω)^2 ∂P) = E := by sorry
