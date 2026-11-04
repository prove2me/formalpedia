-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_uniform_bound
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finite_cap_stopped_terminal_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:09:51.92895+00:00
-- url     : https://prove2.me/theorems/fd9aab6f-fb20-4730-86cd-fcdd11560b0d
-- title:
--   Uniform deterministic bound for original discounted terminal at a finite dividend cap
-- statement:
--   On the actual source Lévy law, finite admissible cap controls the original postpayment-or-ruin reserve. The canonical candidate is bounded on this range by continuity and zero extension, and exp(-q τ) is between zero and one, so the true discounted Term is uniformly bounded over every outcome. No new random moment or probability premise is inserted; unbounded cap remains separate.
-- source:
--   P4-F accepted source reserve cap dd12ff75 and zero-extended finite cap candidate bound 9893589a; Real.exp_le_one_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_zero_extended_continuous_value_bounded_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_reserve_le
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finite_cap_stopped_terminal_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ω, |Term ω| ≤ B := by sorry
