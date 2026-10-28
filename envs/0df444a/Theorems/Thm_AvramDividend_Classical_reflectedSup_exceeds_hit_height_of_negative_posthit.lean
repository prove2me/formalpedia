-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_exceeds_hit_height_of_negative_posthit
-- name    : AvramDividend.Classical.reflectedSup_exceeds_hit_height_of_negative_posthit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:50:39.202317+00:00
-- url     : https://prove2.me/theorems/f74c6a0c-0ba5-408d-aadf-7651ad335bdc
-- title:
--   A genuine spectrally negative Lévy drawdown strictly exceeds any level after an immediate negative process increment
-- statement:
--   For an actual spectrally negative Lévy sample path, suppose its reflected drawdown at time T<ζ equals x. If the underlying Lévy path has strictly negative increments arbitrarily soon after T, the monotonicity of the actual running supremum implies some reflected drawdown value strictly exceeds x at a time between T and ζ. This removes the abstract path S,Y variables from the previously proved deterministic overshoot theorem and serves as the exact pathwise contradiction in the conditional excursion-height atomlessness proof.
-- source:
--   Kuznetsov–Kyprianou–Rivero 2013 Lemma 2.4; Prove2Me reflected-excursion strict-overshoot theorem and runningSup_monotone_and_path_le.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_reflected_excursion_exceeds_hit_height_of_local_negative_increments

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_exceeds_hit_height_of_negative_posthit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T ζ x : ℝ≥0) (hT : T < ζ)
    (hHit : reflectedSup X T ω = (x : ℝ))
    (hNeg : ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X (T + s) ω < X.X T ω) :
    ∃ t : ℝ≥0, T ≤ t ∧ t < ζ ∧
      (x : ℝ) < reflectedSup X t ω := by sorry
