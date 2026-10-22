-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_eq_of_common_tendstoInMeasure
-- name    : AvramDividend.Classical.ae_eq_of_common_tendstoInMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:58:29.719541+00:00
-- url     : https://prove2.me/theorems/0bec8de6-837e-4017-92ab-acc7f9cdc56f
-- title:
--   Almost-everywhere equality of two limits of almost-everywhere equal approximating sequences
-- statement:
--   Let two sequences of real-valued random variables F_n and G_n agree almost everywhere at each index n. If F_n converges in measure to F and G_n converges in measure to G, prove F=G almost everywhere. Transfer the second convergence-in-measure statement across the almost-everywhere equality via the exact Mathlib TendstoInMeasure.congr_left theorem and apply the uniqueness theorem tendstoInMeasure_ae_unique for the countably generated natural-number atTop filter. This is a generic closure lemma needed when simple-function conditional Markov identities F_n=G_n hold at each finite approximation and both sides converge in L1 to their intended general-state limits.
-- source:
--   Pinned Mathlib MeasureTheory.TendstoInMeasure.congr_left and tendstoInMeasure_ae_unique from Mathlib.MeasureTheory.Function.ConvergenceInMeasure.

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open Filter MeasureTheory

theorem AvramDividend.Classical.ae_eq_of_common_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Fn Gn : ℕ → Ω → ℝ) (F G : Ω → ℝ)
    (hEq : ∀ n, Fn n =ᵐ[P] Gn n)
    (hFn : TendstoInMeasure P Fn atTop F)
    (hGn : TendstoInMeasure P Gn atTop G) :
    F =ᵐ[P] G := by sorry
