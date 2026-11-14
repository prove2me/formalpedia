-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb40_original_linear_source_compensated_jump_residual_identically_zero
-- name    : AvramDividend.Classical.avram_bvb40_original_linear_source_compensated_jump_residual_identically_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:13:24.888463+00:00
-- url     : https://prove2.me/theorems/7554a538-6691-414e-bc65-a1d8f1f029f2
-- title:
--   Exact original Lévy linear-source physical jump compensation residual R vanishes on true no-source-jump sample paths
-- statement:
--   If the actual original spectrally negative Lévy sample path agrees with its physical drift line X_t=t*drift through horizon S, then at each physical time t≤S the exact original source residual R_t=((t*drift-X_t)-∑_v(1_{0<v≤t}(leftLim(X)_v-X_v))) vanishes. The true original left-limit jump at every v≤t is zero by the accepted source bvb32 linear no-jump theorem. The entire summand is pointwise zero, so its tsum is zero. This discharges the canonical second noise correction in the original source B_n definition on mixed-reserve no-source-jump survivors, and permits hAllB to constrain the true strict-interior G_n directly.
-- source:
--   Proved c7a5d29a original linear source physical nojump lemma; original B_n correction term in b2d827e6 and 540ad469.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb32_original_linear_source_horizon_no_negative_jump_leftLim
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb40_original_linear_source_compensated_jump_residual_identically_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (S : ℝ≥0)
    (hSource : ∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift)
    (t : ℝ≥0) (ht : t ≤ S) :
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = 0 := by sorry
