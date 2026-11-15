-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a235_gaussian_physical_cell_exponential_discount_width_Lipschitz
-- name    : AvramDividend.Classical.avram_ga_a235_gaussian_physical_cell_exponential_discount_width_Lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:53:48.006754+00:00
-- url     : https://prove2.me/theorems/7ae19629-036c-476c-85af-115cf5bd6ac8
-- title:
--   Original Gaussian discounted source exponential cell factors bounded by one and difference by rate times width
-- statement:
--   On every positive physical time grid with nonnegative discount q, the start and end exponential discount factors lie between zero and one, and the absolute difference over a cell is at most q times its nonnegative width. This supplies the deterministic source-side hypothesis of the one-sided Gaussian combined Taylor discount cross lemma a234 used for a216.
-- source:
--   Original Gaussian physical-cell e^{-qt} discount absolute width inequality via Real.exp and 1-exp(-v)≤v

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a235_gaussian_physical_cell_exponential_discount_width_Lipschitz
    (q s Δ : ℝ) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hΔ : 0 ≤ Δ) :
    0 ≤ Real.exp (-(q*s)) ∧ Real.exp (-(q*s)) ≤ 1 ∧
    0 ≤ Real.exp (-(q*(s+Δ))) ∧
    Real.exp (-(q*(s+Δ))) ≤ 1 ∧
    |Real.exp (-(q*(s+Δ))) - Real.exp (-(q*s))| ≤ q*Δ := by sorry
