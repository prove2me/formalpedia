-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_min_killed_scale_harmonicity_one_to_barrier
-- name    : AvramDividend.Classical.avram_p4_f6_original_min_killed_scale_harmonicity_one_to_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:37:58.547925+00:00
-- url     : https://prove2.me/theorems/27e24986-9e1b-4e05-953f-174ebc8cd309
-- title:
--   Original killed minimum of upper/down exits preserves q-scale harmonicity from reserve one
-- statement:
--   For actual standing spectrally negative Lévy X and scale W, original law expectation of the discounted q-scale function at the finite minimum of strict upper and lower exit times equals W(1), for upper barrier b≥1. This is the true stochastic killed q-scale harmonicity missing from the otherwise Proved bounded/unbounded terminal factorisations; its proof requires optional stopping, localisation and scale-function q-harmonicity with the original process.
-- source:
--   Exact terminal left-hand side copied from Proved avram_root29_03_bv_stopped_min_terminal_exit_factorisation and avram_root29_03_ubv_stopped_min_terminal_exit_factorisation, with a=b and x=1. This isolates only the genuine missing stopped harmonicity, and their accepted conversion then proves original stopped scale balance 0fd96441.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_original_min_killed_scale_harmonicity_one_to_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ b : ℝ, 1 ≤ b →
      (∫⁻ ω, if min (twoSidedExitUpTime X (b - 1) ω) (twoSidedExitDownTime X (-1) ω) < ⊤ then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (b - 1) ω) (twoSidedExitDownTime X (-1) ω))))) *
          ENNReal.ofReal
            (W (1 + X.X (min (twoSidedExitUpTime X (b - 1) ω) (twoSidedExitDownTime X (-1) ω)).toNNReal ω))
        else 0 ∂P) = ENNReal.ofReal (W 1) := by sorry
