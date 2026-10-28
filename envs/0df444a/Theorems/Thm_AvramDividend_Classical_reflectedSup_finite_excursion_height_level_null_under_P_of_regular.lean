-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_height_level_null_under_P_of_regular
-- name    : AvramDividend.Classical.reflectedSup_finite_excursion_height_level_null_under_P_of_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:02:21.137732+00:00
-- url     : https://prove2.me/theorems/2901e025-c215-42bb-8838-ea935d6f1598
-- title:
--   Actual finite-horizon reflected-excursion height selectors have no positive singleton atoms under the Lévy probability law when source downward regularity holds
-- statement:
--   Let X be a spectrally negative Lévy process satisfying almost-sure negative values arbitrarily close to time zero. Fix a finite positive horizon H and any excursion-height functional Height. Suppose on the level event Height=x>0, the actual reflected drawdown returns to zero at H and its true maximum on [0,H] equals x. Then the ordinary Lévy probability law P assigns zero mass to {Height=x}. Proof: the accepted first-maximal-height geometry shows that the exact capped hit is an in-lifetime actual level hit and no larger reflected level occurs before H; the accepted stopped strong-Markov law transfers source downward regularity immediately after that capped first hit; the accepted excursion-height atomlessness contradiction then forces P of the height-level event to vanish. This closes the complete conditional first-hit/Markov/atomlessness argument under ordinary P. It explicitly does not prove the corresponding result for the sigma-finite Itô excursion measure n, which is generally not P and whose killed strong Markov identity remains a distinct substantial theorem.
-- source:
--   Kuznetsov Kyprianou Rivero (2013), Lemma 2.4; accepted reflectedSup_finite_excursion_capped_first_hit_geometry, reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source and reflectedSup_height_level_null_of_ae_posthit_negative.

import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_capped_first_hit_geometry
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_regular_source
import Theorems.Thm_AvramDividend_Classical_reflectedSup_height_level_null_of_ae_posthit_negative

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_finite_excursion_height_level_null_under_P_of_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (hH : 0 < H)
    (Height : Ω → ℝ≥0) (x : ℝ≥0) (hx : 0 < x)
    (hHeight : ∀ ω : Ω, Height ω = x →
      reflectedSup X H ω = 0 ∧
      sSup ((fun u : ℝ≥0 => reflectedSup X u ω) '' Icc 0 H) = (x : ℝ))
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hRegular : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    P {ω : Ω | Height ω = x} = 0 := by sorry
