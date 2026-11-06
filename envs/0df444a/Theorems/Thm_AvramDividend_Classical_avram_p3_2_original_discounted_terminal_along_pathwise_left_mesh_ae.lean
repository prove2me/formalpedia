-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_terminal_along_pathwise_left_mesh_ae
-- name    : AvramDividend.Classical.avram_p3_2_original_discounted_terminal_along_pathwise_left_mesh_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:17:14.929826+00:00
-- url     : https://prove2.me/theorems/8673b218-d173-4849-a908-c74fa5900215
-- title:
--   Original discounted horizon reserve along sample-dependent strict left meshes
-- statement:
--   For original X and capped admissible D, any sample-dependent sequence of strictly pre-horizon observation times converging pathwise to a positive deterministic T inherits the almost-sure limit of discounted w of the postpayment reserve to the actual discounted pre-rightpayment horizon reserve on strict survival.
-- source:
--   Use the fully Proved P3-2 original discounted terminal left convergence at fixed T and compose pathwise with each sample's strict-left observation mesh, converting its nhds convergence plus strict inequality to nhdsWithin. This handles potentially random crossing indices without assuming equality in law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_survivor_pre_rightpayment_terminal_left_tendsto_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_discounted_terminal_along_pathwise_left_mesh_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (u : Ω → ℕ → ℝ≥0)
    (hu : ∀ ω n, u ω n < t)
    (huLimit : ∀ ω, Tendsto (u ω) atTop (𝓝 t)) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun n : ℕ =>
        Real.exp (-(q * (u ω n : ℝ))) *
          w (x + X.X (u ω n) ω - rightLimit D (u ω n) ω))
        atTop
        (𝓝 (Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω))) := by sorry
