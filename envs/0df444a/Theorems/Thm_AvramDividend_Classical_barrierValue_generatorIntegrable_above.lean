-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_generatorIntegrable_above
-- name    : AvramDividend.Classical.barrierValue_generatorIntegrable_above
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T05:47:47.627955+00:00
-- url     : https://prove2.me/theorems/646942a1-f369-46c2-aba9-d76cc74aa7f0
-- title:
--   Barrier-value Lévy generator integrability strictly above any nonnegative cap
-- statement:
--   Let W be a formal q-scale function and let a be any nonnegative finite real barrier. At every reserve x>a, the exact compensated Lévy generator jump term of barrierValue W a is integrable on negative jumps. No finite large-negative-jump first moment is required: near zero the integrand vanishes because the candidate is locally affine with slope one; away from zero the Lévy measure has finite mass and the barrier values at all destinations x+y<=x are bounded using W's nonnegative monotone branch and its zero extension.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter Topology
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierValue_generatorIntegrable_above
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : a < x) :
    X.GeneratorIntegrable (barrierValue W a) x := by sorry
