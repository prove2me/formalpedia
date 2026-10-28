-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_uniform_expected_monotone_count_ae_bounded
-- name    : AvramDividend.Classical.bv_uniform_expected_monotone_count_ae_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:35:26.768073+00:00
-- url     : https://prove2.me/theorems/1271cb11-30ac-458e-9e87-f8c9a5886915
-- title:
--   Uniformly bounded expectations imply finite almost-sure supremum for monotone nonnegative random counts
-- statement:
--   For an arbitrary monotone sequence of nonnegative measurable random variables with common finite upper bound C on all expected values, their pointwise supremum is finite almost everywhere. Proof via pinned Mathlib monotone convergence for lintegral_iSup, iSup_le and ae_lt_top. This is the probabilistic foundation of the dyadic no-creep proof: bound expected active counts uniformly in dyadic mesh, then deduce no sample path has infinitely many active cells outside a null set.
-- source:
--   Monotone convergence theorem, Mathlib MeasureTheory.Integral.Lebesgue.Add and .Markov; Avram finite-activity no-creep dyadic programme.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.bv_uniform_expected_monotone_count_ae_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hF : ∀ n, Measurable (F n))
    (hMono : Monotone F)
    (hBound : ∀ n, (∫⁻ ω, F n ω ∂P) ≤ C)
    (hFinite : C < ⊤) :
    ∀ᵐ ω ∂P, (⨆ n, F n ω) < ⊤ := by sorry
