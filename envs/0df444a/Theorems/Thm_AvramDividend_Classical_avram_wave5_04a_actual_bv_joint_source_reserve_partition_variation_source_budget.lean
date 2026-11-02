-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_joint_source_reserve_partition_variation_source_budget
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_joint_source_reserve_partition_variation_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:33:28.000445+00:00
-- url     : https://prove2.me/theorems/5013dbe7-bab0-403b-ae3c-453066f6ca16
-- title:
--   Joint original source-remainder and controlled reserve variation bounded by actual source and dividends
-- statement:
--   For the genuine spectrally negative Levy process under Standing and bounded variation and any actual left-continuous monotone dividend strategy, a single almost-sure event carries an explicitly defined monotone original-source residual R and a joint finite-partition total-variation bound for R and the true controlled reserve. The right side involves only observed source increments, source drift and the strategy's chronological dividend increments, not an unobserved remainder. This supplies a uniform C1 controlled-chain-rule variation budget and does not assume Ito-Meyer or pure-jump equality.
-- source:
--   Chat04-A actual BV variation joint event combining Proved original residual partition variation 3ddc1a4c-7733-4bfe-82ec-284764e67394, original-source interval decomposition c4b53c7c-d769-4894-a0d8-c0b2a1516d1e, and independently Proved actual controlled BV variation 2faae607-6a38-40ab-a87f-de5c4dbf9672. Witnesses are aligned using the explicit source residual definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_partition_variation

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Source-residual plus true controlled-reserve variation is bounded by
observable original-source drift and increments and chronological dividends;
the event is uniform over every finite ordered partition. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_joint_source_reserve_partition_variation_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (Finset.range n).sum (fun i =>
          |R (u (i + 1)) - R (u i)|) +
        (Finset.range n).sum (fun i =>
          |riskProcess X x D (u (i + 1)) ω -
            riskProcess X x D (u i) ω|) ≤
        (((u n : ℝ) - (u 0 : ℝ)) * X.drift -
          (X.X (u n) ω - X.X (u 0) ω)) +
        (2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
          (X.X (u n) ω - X.X (u 0) ω) +
          (D (u n) ω - D (u 0) ω)) := by sorry
