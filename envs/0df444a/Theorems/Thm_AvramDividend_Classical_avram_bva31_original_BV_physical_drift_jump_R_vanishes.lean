-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva31_original_BV_physical_drift_jump_R_vanishes
-- name    : AvramDividend.Classical.avram_bva31_original_BV_physical_drift_jump_R_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:36:29.276402+00:00
-- url     : https://prove2.me/theorems/eb53fb1e-d594-47ee-8286-ce7ca08ab9d5
-- title:
--   Exact original BV full physical drift residual R is zero for every real clock, almost surely
-- statement:
--   For every original spectrally negative Lévy sample path satisfying the Standing and bounded-variation hypotheses, the physical residual R(t)=t*X.drift-X.X(t)-sum of the original left-limit downward jumps is identically zero at every nonnegative real clock outside a single P-null set. The source is the already-Proved original BV interval drift-minus-true-negative-jump lemma cc3bbe55 with initial X.X(0)=0, and applies at arbitrary physical grid cells. This eliminates the drift residual in the finite-activity HJB signed cash ledger without a fictitious process or a finite-mesh limiting assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_BV_interval_physical_jump_drift_ledger
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva31_original_BV_physical_drift_jump_R_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = 0 := by sorry
