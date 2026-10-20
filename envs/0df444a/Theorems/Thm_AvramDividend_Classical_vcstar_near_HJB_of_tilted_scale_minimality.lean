-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_tilted_scale_minimality
-- name    : AvramDividend.Classical.vcstar_near_HJB_of_tilted_scale_minimality
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T14:19:25.474699+00:00
-- url     : https://prove2.me/theorems/8513e6c4-84c2-4114-aa86-70f28c24524f
-- title:
--   Near-barrier dividend HJB from positive tilted scale monotonicity and derivative minimality
-- statement:
--   For positive q and positive real canonical cstar, suppose the q-scale W is continuously differentiable on positive capital, strictly positive there, and its exponential tilt exp(-φx)W(x) is monotone for some φ>0, with the exact canonical derivative minimality property. For every reserve x>cstar with x≥1 and x≥cstar+max(0,X.c/q), the true nonlocal generator of vcstar is integrable and the full dividend HJB maximum equals zero. The key point is that the Proved derivative bound v'≥1 on positive reserves and continuity below the cap imply the previously conditional left affine-majorant inequality by a mean-value theorem, thereby discharging that condition. It does not claim the structural tilt/strict-positivity assumptions follow automatically from bare IsScaleFunction.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_near_HJB_of_tilted_scale_minimality
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpositive : ∀ x : ℝ, 0 < x → 0 < W x)
    (φ : ℝ) (hφ : 0 < φ)
    (htilt : MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x))
    (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
