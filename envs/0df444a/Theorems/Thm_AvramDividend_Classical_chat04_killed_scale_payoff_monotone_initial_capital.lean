-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_monotone_initial_capital
-- name    : AvramDividend.Classical.chat04_killed_scale_payoff_monotone_initial_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:39:40.09231+00:00
-- url     : https://prove2.me/theorems/91cb3eb1-7336-4d04-9352-78a135b462e0
-- title:
--   Whole-path killed scale reward is monotone in initial reserve
-- statement:
--   For a spectrally negative Lévy process and its globally monotone scale function, the nonnegative discounted q-scale payoff gated by survival through the entire interval increases pointwise with initial reserve. This is the key domination allowing zero-capital renewal to be obtained as the limit of strictly positive-capital renewal without a separate instantaneous-downcrossing regularity theorem.
-- source:
--   Proved scaleFunction_monotone, elementary survival event inclusion and monotonicity of ENNReal.ofReal.

import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_scale_payoff_monotone_initial_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x y : ℝ) (hxy : x ≤ y) (t : ℝ≥0) (ω : Ω) :
    ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
      (fun u => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ≤
    ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s u}).indicator
      (fun u => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (y + X.X t u))) ω := by sorry
