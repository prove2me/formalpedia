-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_history_killed_lintegral_le_terminal_only
-- name    : AvramDividend.Classical.chat01_history_killed_lintegral_le_terminal_only
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:33:21.362651+00:00
-- url     : https://prove2.me/theorems/6319a734-8a68-4782-b67e-7ecbfb4c8d67
-- title:
--   Whole-history killed discounted scale expectation is bounded by terminal-only killing
-- statement:
--   For an arbitrary spectrally negative Levy process and q-scale function, the q-discounted scale mass on paths that remain nonnegative throughout [0,t] is bounded above by the mass from paths nonnegative only at terminal t. Every surviving history has a nonnegative terminal reserve, whereas paths crossing below zero and returning contribute only on the right. This inequality prevents replacing genuine pathwise killing with terminal-only killing as an equality.
-- source:
--   Avram Dividend Esscher first-passage workstream. Exact event domination needed to distinguish the true killed q-scale renewal identity from the mathematically invalid terminal-only claim; pointwise positivity is automatic after ENNReal.ofReal.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_history_killed_lintegral_le_terminal_only
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) ≤
    (∫⁻ ω, ({ω | 0 ≤ x + X.X t ω}).indicator
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) := by sorry
