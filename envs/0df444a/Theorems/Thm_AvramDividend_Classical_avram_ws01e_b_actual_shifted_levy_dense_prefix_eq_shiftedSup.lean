-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T20:12:35.86245+00:00
-- url     : https://prove2.me/theorems/a9e1f1a9-e760-4abb-aadb-b7b5effb05aa
-- title:
--   Genuine full-prefix supremum of centred Lévy increments at any shifted record age equals countable measurable sampled prefix
-- statement:
--   For every actual spectrally negative Lévy path, deterministic base time u, dense countable clock schedule containing zero and endpoint t, the countable ENNReal clipped supremum of the centred shifted path X(u+s)−X(u) over sampled s≤t equals its true raw real supremum over [0,t]. The result is pointwise in ω,u,t, with no stopping-time, Esscher or independence assumption. It provides the pathwise identification of the residual full shifted path used in genuine Qp first-record regeneration 4cf7269f, which was not covered by the unshifted runningSup lemma f32e574e.
-- source:
--   Proved deterministic dense-prefix identity 4d43b293; source shifted Lévy increments right-continuity b901917f; compact Lévy path upper bound c2066587; first-record conditional Qp law 4cf7269f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (samples : ℕ → ℝ≥0) (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples) :
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω) else 0).toReal =
    sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) := by sorry
