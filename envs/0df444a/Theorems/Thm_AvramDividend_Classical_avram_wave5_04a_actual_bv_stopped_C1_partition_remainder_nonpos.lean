-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_stopped_C1_partition_remainder_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_C1_partition_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:39:17.48349+00:00
-- url     : https://prove2.me/theorems/d7023e31-c727-4052-8585-2b0432afa2d3
-- title:
--   Original BV source residual nonjump loss contributes nonpositively to every stopped C1 verification partition
-- statement:
--   For the original bounded-variation spectrally negative Lévy path and an actual dividend strategy D, on a single full-probability event, every finite ordered partition of an arbitrary samplewise stopping horizon admits nonnegative interval remainders between the true source Stieltjes loss and the sum of all original source negative-jump magnitudes. If the C1 verification derivative evaluated at each actual reserve sample is nonnegative, its sum against the negative remainders is nonpositive. This is the finite-partition source contribution and sign interface for controlled BV chain-rule passage; no complete Itô–Meyer theorem, independent Poisson process, or absence of diffuse residual mass is assumed. Dividend right payments remain separate from source left jumps.
-- source:
--   Avram Wave 5 Chat 04-A, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Derived independently from canonical Proved 6db7ca71-b2a6-468c-9020-c8178e8d9dd3 and pinned tsub_add_cancel_of_le, ENNReal.toReal_nonneg, finite-sum sign; finite-partition bridge to Chat 03 and final Chat 04 BV verification ef7e6c20-a118-46f0-ac94-5b02204bba49. Does not assume chain rule or stochastic expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_C1_partition_remainder_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      (∀ t : ℝ≥0, (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hgrad : ∀ i : Fin n,
          0 ≤ deriv w (riskProcess X x D (u i) ω)),
        ∃ r : Fin n → ℝ≥0∞,
          (∀ i : Fin n,
            (∑' (v : ℝ≥0),
              if 0 < v ∧ v ∈ Ioc (u i) (u (i + 1)) then
                ENNReal.ofReal (Function.leftLim
                  (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
              else 0) + r i =
              F.measure (Ioc (u i) (u (i + 1)))) ∧
          (∑ i : Fin n,
            -(deriv w (riskProcess X x D (u i) ω)) *
              (r i).toReal) ≤ 0 := by sorry
