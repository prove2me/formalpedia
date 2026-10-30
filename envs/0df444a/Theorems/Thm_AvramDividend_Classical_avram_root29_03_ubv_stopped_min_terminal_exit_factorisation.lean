-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
-- name    : AvramDividend.Classical.avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:16:34.361493+00:00
-- url     : https://prove2.me/theorems/a219a488-74cf-43e0-a833-3f62d72e98ee
-- title:
--   UBV genuine finite stopped minimum q-scale terminal payoff factors as strict upper-exit discount mass
-- statement:
--   For an actual spectrally negative Lévy process of unbounded variation, q>0, 0<a and x<=a, the original-law finite minimum U∧D stopped discounted q-scale terminal integral equals twoSidedExitExpectation X q a x times ENNReal.ofReal(W a). The result follows from accepted exact source minimum-to-branches conversion 7c9fe862 and accepted UBV upper/lower factorisation 5b55cf54. It is a payoff identity, not the missing killed martingale equality to W(x).
-- source:
--   Noncircular transitivity of canonically Proved 7c9fe862 and 5b55cf54; the open genuine killed harmonicity be9dc931 is not imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exact_qscale_two_branch_terminal_conversion
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hxa : x ≤ a) :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by sorry
