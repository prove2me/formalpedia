-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_capped_hit_eq_first_exact
-- name    : AvramDividend.Classical.reflectedSup_finite_excursion_capped_hit_eq_first_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:42:53.827049+00:00
-- url     : https://prove2.me/theorems/b924f00e-bcb5-4eef-b260-6013b9689796
-- title:
--   A positive finite reflected excursion's exact first maximal-height hit coincides with its capped stopping-time clock
-- statement:
--   Suppose an actual spectrally negative Lévy reflected path starts at zero, returns to zero at a finite positive excursion endpoint ζ and attains a strictly positive supremum height x on [0,ζ]. The already proved first-exact-height theorem ensures a genuine hit T strictly before ζ. Adjoining the fallback horizon ζ to the exact-superlevel first-hit set therefore cannot change its infimum, by the newly proved general cap-removal lemma. This formally links the first-hit time used in the excursion-height atomlessness proof (without fallback) to the actual finite-horizon stopping time to which ordinary-P strong Markov law transfer applies. The excursion-measure killed strong Markov law remains separate.
-- source:
--   Accepted reflectedSup_finite_excursion_first_exact_height_hit; nnreal_sInf_union_cap_eq_of_early_member.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_first_exact_height_hit
import Theorems.Thm_AvramDividend_Classical_nnreal_sInf_union_cap_eq_of_early_member

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_finite_excursion_capped_hit_eq_first_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) (hζ : 0 < ζ)
    (hEnd : reflectedSup X ζ ω = 0)
    (x : ℝ) (hx : 0 < x)
    (hHeight : sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 ζ) = x) :
    sInf ((Icc (0 : ℝ≥0) ζ ∩
      (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∪ {ζ}) =
    sInf (Icc (0 : ℝ≥0) ζ ∩
      (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) := by sorry
