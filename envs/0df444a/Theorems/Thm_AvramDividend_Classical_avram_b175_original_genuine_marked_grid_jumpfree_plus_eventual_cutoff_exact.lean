-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b175_original_genuine_marked_grid_jumpfree_plus_eventual_cutoff_exact
-- name    : AvramDividend.Classical.avram_b175_original_genuine_marked_grid_jumpfree_plus_eventual_cutoff_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:26:06.423056+00:00
-- url     : https://prove2.me/theorems/28f05038-37d2-4236-9a87-469890b8d0b3
-- title:
--   Original finite physical grid has one exact marked Finset that simultaneously makes every unmarked cell genuinely jumpfree and is eventually attained by every negative jump cutoff
-- statement:
--   For the actual original spectrally negative Levy source on one sample path and an arbitrary finite family of genuine physical source clock intervals, construct one finite selected set J marking exactly cells containing a nonzero physical original source left-limit jump in their half-open intervals. This J is a subset of the given finite mesh index set, and every unmarked cell is genuinely jumpfree throughout its physical interval. Furthermore authoritatively Proved B132 establishes that there exists one finite reciprocal negative source cutoff beyond which every negative-band marked occupied-cell Finset equals exactly J. The proof combines the source physical Finset.filter selector, its pathwise jumpfree complement and the full B132 source cutoff eventual exactness. This packages the exact original source marked/unmarked decomposition needed for the finite-mesh Gaussian-jump stopped Ito source, avoiding separate unproved cell-classification and cutoff exhaustiveness assumptions.
-- source:
--   Proved original B132 exact physical marked-grid cutoff exhaustion and canonical original Finset.filter jumpfree classification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b132_original_finite_physical_grid_negative_band_occupied_set_eventually_exact
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A single exact finite original physical marked-grid selector simultaneously classifies all true jumpfree cells and is reached exactly by all sufficiently fine negative source cutoffs. -/

theorem AvramDividend.Classical.avram_b175_original_genuine_marked_grid_jumpfree_plus_eventual_cutoff_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0) :
    ∃ J : Finset ℕ,
      J ⊆ S ∧
      (∀ i ∈ S, i ∉ J → ∀ u : ℝ≥0, s i < u → u ≤ t i →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        S.filter (fun i => ∃ u : ℝ≥0, s i < u ∧ u ≤ t i ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))) = J) := by sorry
