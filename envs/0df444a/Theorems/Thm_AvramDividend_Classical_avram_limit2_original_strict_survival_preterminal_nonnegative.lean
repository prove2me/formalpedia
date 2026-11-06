-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_survival_preterminal_nonnegative
-- name    : AvramDividend.Classical.avram_limit2_original_strict_survival_preterminal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:07:51.665146+00:00
-- url     : https://prove2.me/theorems/28d21985-1c22-43f1-a2a0-0649a4625021
-- title:
--   Nonnegative exact original strictly surviving pre-rightpayment terminal at positive real horizons
-- statement:
--   Publication repair of failed job 53d7d0fd-c05c-4737-b3b8-873c6ad68e0a: the original statement used an inline subtype pair where riskProcess expected an ENNReal-coercible argument. Bind the source-exact NNReal horizon S=⟨T,hT⟩ once, then use (S:ENNReal) for ruin survival and S for riskProcess. The same hw_nonneg hypothesis and positive exponential show the original terminal is nonnegative on surviving paths, while other paths contribute exact zero.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_strict_survival_preterminal_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ ω, 0 ≤
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) := by sorry
