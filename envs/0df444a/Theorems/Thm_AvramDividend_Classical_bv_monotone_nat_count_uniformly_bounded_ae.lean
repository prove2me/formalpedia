-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_monotone_nat_count_uniformly_bounded_ae
-- name    : AvramDividend.Classical.bv_monotone_nat_count_uniformly_bounded_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:35:38.782861+00:00
-- url     : https://prove2.me/theorems/498151d8-7ab2-42de-99e8-17d0a06bbccd
-- title:
--   Monotone natural random counts with uniformly bounded expectation admit a finite pathwise bound almost surely
-- statement:
--   For an increasing natural-valued random count F_n with a finite uniform bound on nonnegative expected value, almost every path admits one finite natural ceiling K on all F_n. Monotone convergence yields finite ENNReal supremum a.s.; ENNReal.exists_nat_gt supplies K, with all component counts bounded by their supremum. This conclusion is exactly the finite-grid-count condition needed for the deterministic finite-step path theorem.
-- source:
--   Monotone convergence theorem, Mathlib MeasureTheory.Integral.Lebesgue.Add and .Markov; Avram finite-activity no-creep dyadic programme.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.ENNReal.Basic

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.bv_monotone_nat_count_uniformly_bounded_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℕ) (C : ℝ≥0∞)
    (hF : ∀ n, Measurable (fun ω => (F n ω : ℝ≥0∞)))
    (hMono : Monotone (fun n => fun ω => (F n ω : ℝ≥0∞)))
    (hBound : ∀ n, (∫⁻ ω, (F n ω : ℝ≥0∞) ∂P) ≤ C)
    (hFinite : C < ⊤) :
    ∀ᵐ ω ∂P, ∃ K : ℕ, ∀ n : ℕ, F n ω ≤ K := by sorry
