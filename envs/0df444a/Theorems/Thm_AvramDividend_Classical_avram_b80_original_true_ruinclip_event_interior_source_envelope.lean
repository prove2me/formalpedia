-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b80_original_true_ruinclip_event_interior_source_envelope
-- name    : AvramDividend.Classical.avram_b80_original_true_ruinclip_event_interior_source_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:01:37.922135+00:00
-- url     : https://prove2.me/theorems/33cfcf50-f678-445b-9f0e-b65db40d9228
-- title:
--   Original true ruin-clipped physical source compact interior envelope restricted to good event
-- statement:
--   Exact original physical ruin-clipped source envelope on any GOOD EVENT, rather than on every sample path. The event can require positive original stopped clock and exclude its zero-clock and final crossing cases. For each sample path in that event, each selected fixed grid cell whose right endpoint is STRICTLY BEFORE actual kappa has both endpoints before actual ruin and original upper source exit, and their genuine X source values are at least minus initial surplus. The original clipped time bounds all endpoints by n. This removes the global-for-all-omega interior index hypothesis of B72 and supplies the exact event-side compact source conditions for the forthcoming B79 event-restricted mixed energy theorem. No assumptions on event measurability are needed for the deterministic pointwise conclusion, although later stochastic integration does require it.
-- source:
--   Original Proved B65 and B69 exact physical stopped source, Avram Palmowski Pistorius 2007 Proposition 4(i) terminal ruin clipping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b65_original_strict_preruin_X_lower
import Theorems.Thm_AvramDividend_Classical_avram_b69_original_true_spatial_clock_ruin_clipped
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b80_original_true_ruinclip_event_interior_source_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (A : Set Ω) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hInterior : ∀ ω ∈ A, ∀ i ∈ S,
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞)) :
    ∀ ω ∈ A, ∀ i ∈ S,
      (s i ω ≤ t i ω ∧ t i ω ≤ (n : ℝ≥0)) ∧
      (-x ≤ X.X (s i ω) ω ∧ -x ≤ X.X (t i ω) ω) ∧
      ((s i ω : ℝ≥0∞) <
         twoSidedExitUpTime X ((k : ℝ) + 1) ω ∧
       (t i ω : ℝ≥0∞) <
         twoSidedExitUpTime X ((k : ℝ) + 1) ω) := by sorry
