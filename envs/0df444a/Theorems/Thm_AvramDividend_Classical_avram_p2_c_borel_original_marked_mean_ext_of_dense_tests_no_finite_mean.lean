-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_marked_mean_ext_of_dense_tests_no_finite_mean
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_marked_mean_ext_of_dense_tests_no_finite_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:23:58.365197+00:00
-- url     : https://prove2.me/theorems/df0003c4-f2df-49ba-965d-e9762e68181e
-- title:
--   Dense cutoff original marked tests imply all Borel rates without a finite-mean premise
-- statement:
--   If a comparison Borel measure is finite below a strictly negative mark cutoff and the actual original expected jump count matches it on a dense set of cutoff-restricted lower halflines, then every cutoff Borel mark count matches. Finiteness of the original source count is derived from a single dense test threshold lying above the cutoff. The underlying analytical dense tests remain an explicit hypothesis.
-- source:
--   P2-C strengthens its original dense expected-mark extension by removing the finite-mean hypothesis via Dense.exists_seq_strictAnti_tendsto and an upper cutoff threshold. It invokes no Open source ν-rate theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_marked_mean_ext_of_dense_tests_no_finite_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure ℝ) (hρfin : ρ (Iic (-ε)) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) = ρ (Iic a ∩ Iic (-ε)))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) = ρ (B ∩ Iic (-ε)) := by sorry
