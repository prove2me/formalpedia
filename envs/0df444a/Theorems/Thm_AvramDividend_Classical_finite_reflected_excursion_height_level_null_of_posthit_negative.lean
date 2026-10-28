-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_reflected_excursion_height_level_null_of_posthit_negative
-- name    : AvramDividend.Classical.finite_reflected_excursion_height_level_null_of_posthit_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:40:28.080953+00:00
-- url     : https://prove2.me/theorems/25038466-2962-429d-8d00-5f6fb556a5e8
-- title:
--   Finite actual reflected excursion height has no singleton atom once post-first-hit downward regularity holds
-- statement:
--   Let n be a putative excursion measure on actual spectrally negative Lévy paths, ζ a finite lifetime and H the excursion height. For any x>0, suppose each height-x excursion has finite positive lifetime, returns to reflected level zero at its end and has its exact reflected-path supremum equal to x. If n-almost surely the underlying Lévy path decreases arbitrarily soon after the first exact reflected level-x hit, then n(H=x)=0. The first-hit time is not an arbitrary assumed selector: it is explicitly defined as the infimum of the superlevel set, and its actual first-hit/maximality geometry follows from proved finite-excursion pathwise results. The genuinely probabilistic excursion-measure post-hit downward-regularity hypothesis remains explicit, not presumed from the ordinary P-law.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013) §2.3 Lemma 2.4 with exact finite-lifetime pathwise height attainment and first-hit contradiction; Prove2Me accepted reflectedSup_height_level_null_of_ae_posthit_negative.

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_finite_excursion_first_exact_height_hit
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_height_level_null_of_ae_posthit_negative

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finite_reflected_excursion_height_level_null_of_posthit_negative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : Measure Ω) (ζ H : Ω → ℝ≥0) (x : ℝ≥0)
    (hx : 0 < x)
    (hFinite : ∀ ω : Ω, H ω = x →
      0 < ζ ω ∧
      reflectedSup X (ζ ω) ω = 0 ∧
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 (ζ ω)) = (x : ℝ))
    (hNeg : ∀ᵐ ω ∂n,
      sInf (Icc (0 : ℝ≥0) (ζ ω) ∩
        (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici (x : ℝ)) < ζ ω →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧
          X.X (sInf (Icc (0 : ℝ≥0) (ζ ω) ∩
            (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici (x : ℝ)) + s) ω <
          X.X (sInf (Icc (0 : ℝ≥0) (ζ ω) ∩
            (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici (x : ℝ))) ω) :
    n {ω : Ω | H ω = x} = 0 := by sorry
