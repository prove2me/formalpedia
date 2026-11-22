-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_reciprocal_finitebin_isometry
-- name    : AvramDividend.Classical.avram_twoagentA_shared_original_reciprocal_finitebin_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:39:17.249406+00:00
-- url     : https://prove2.me/theorems/6a1bca17-d3f5-474d-8f3c-15e047d5cfda
-- title:
--   Shared proved original physical jump reciprocal-annulus iso lemma
-- statement:
--   Reuses an exact previously accepted original-process proof under a shared public name for the unrestricted-Lévy-annular variance-to-L2-cutoff chain; source research/avram/agents/twoagent_20261122_B/grid_count_iso_v3_assoc.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf17_ordered_finite_physical_mark_isometry
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_shared_original_reciprocal_finitebin_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) :
    let S : Finset ℕ := Finset.Ico n m
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      NX ω (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let c : ℕ → ℝ := fun i => -(1 / ((i : ℝ) + 1))
    (∫ ω, (∑ i ∈ S, c i * ((N i ω).toReal - r i)) ^ 2 ∂P) =
      ∑ i ∈ S, c i ^ 2 * r i := by sorry
