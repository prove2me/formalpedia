-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_discounted_scale_pathwise_cocycle
-- name    : AvramDividend.Classical.chat04_killed_discounted_scale_pathwise_cocycle
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:26:46.458885+00:00
-- url     : https://prove2.me/theorems/bd643e0e-a623-4a28-b3ad-b57892378c7c
-- title:
--   Exact discounted killed q-scale payoff cocycle across a deterministic time split
-- statement:
--   The killed q-scale payoff discounted to u factors pathwise at any s≤u into the survival-to-s indicator, the discount through s, the survival on [s,u] indicator in increment coordinates, and the residual discount from s to u. This exact equality preserves the full continuous path survival condition and is a reusable bridge for the stopped-martingale conditional law.
-- source:
--   Avram classical two-sided exit proof; Proved chat04_lower_killing_indicator_factorisation and exponential discount semigroup property.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_lower_killing_indicator_factorisation
open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_discounted_scale_pathwise_cocycle
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    ({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) =
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (s : ℝ))) *
          ({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
            0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
            (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
              W (x + X.X u ω)) ω) := by sorry
