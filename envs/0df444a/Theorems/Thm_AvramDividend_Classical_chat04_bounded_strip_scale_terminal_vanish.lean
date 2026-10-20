-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_bounded_strip_scale_terminal_vanish
-- name    : AvramDividend.Classical.chat04_bounded_strip_scale_terminal_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:12:06.87598+00:00
-- url     : https://prove2.me/theorems/46c83935-974a-4c44-8449-ac2006564219
-- title:
--   Discounted q-scale terminal rewards vanish along any bounded nonnegative reserve sequence
-- statement:
--   Fix any q>0 and a q-scale function W for a spectrally negative Lévy process. For an arbitrary sequence of reserves y_n satisfying 0≤y_n≤a, the discounted terminal scale reward exp(−qn) W(y_n) tends to zero. This is uniform over the reserve's trajectory: the q-scale function is nonnegative and nondecreasing on [0,∞), hence 0≤W(y_n)≤W(a), so squeeze between zero and W(a)exp(−qn). This supplies the deterministic unexited-terminal residual limit after stopping by increasing integer horizons, without requiring a martingale or independence hypothesis.
-- source:
--   Published IsScaleFunction definition e6610c46-99bb-43cf-af87-4d07e25d1631; exact Real.tendsto_exp_neg_atTop_nhds_zero in Mathlib.Analysis.SpecialFunctions.Exp at pinned revision 0df444a360eaa60ab8c11dca51a86af692955474; Mathlib squeeze_zero theorem. Complements the proved finite-horizon terminal bound UUID 45d66d53-354e-4d29-9b77-c80ac6be3fec.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_bounded_strip_scale_terminal_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (y : ℕ → ℝ)
    (hy : ∀ n, 0 ≤ y n ∧ y n ≤ a) :
    Tendsto (fun n : ℕ =>
      Real.exp (-(q * (n : ℝ))) * W (y n)) atTop (𝓝 0) := by sorry
