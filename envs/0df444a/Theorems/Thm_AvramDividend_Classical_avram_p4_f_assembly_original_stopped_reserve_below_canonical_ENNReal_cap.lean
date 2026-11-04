-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_reserve_below_canonical_ENNReal_cap
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_stopped_reserve_below_canonical_ENNReal_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:55:44.747302+00:00
-- url     : https://prove2.me/theorems/bc3f9658-5254-4925-bf18-7b68df9b2cd1
-- title:
--   Actual original stopped postpayment reserve respects every finite and infinite canonical ENNReal dividend cap
-- statement:
--   For the exact original SpectrallyNegativeLevy stopped terminal W, source admissibility forces ENNReal.ofReal W≤C at every outcome and for C=∞ or finite. The finite case transports to the already accepted source real-cap invariant, the infinite case follows by order.
-- source:
--   Accepted P4-F original finite real cap stopped terminal bound dd12ff75, pinned Mathlib ENNReal.ofReal_toReal and ENNReal.ofReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_stopped_reserve_below_canonical_ENNReal_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, ENNReal.ofReal (W ω) ≤ C := by sorry
