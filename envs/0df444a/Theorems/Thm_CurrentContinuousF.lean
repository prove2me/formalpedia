-- Prove2me | Theorems.Thm_CurrentContinuousF
-- name    : CurrentContinuousF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:54:38.874493+00:00
-- url     : https://prove2.me/theorems/16af0957-b1d1-4ea4-9aa9-54eec7ace5c5
-- title:
--   Current Continuous F: Current Continuous F
-- statement:
--   A metric `1`-current `T` is continuous with respect to pointwise convergence of `f` (with
--   uniformly bounded sup-norms), holding `π` fixed: the `f`-slot mirror of `MetricCurrent1.continuous_pi`
--   (paper.tex 1393, "the continuity with respect to [f_converge] follows from [massmeasure] and
--   Lebesgue's dominated convergence theorem").
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentContinuousF.lean#L11-L88
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentContinuousF.lean#L11-L88

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_CurrentContinuousF
set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
open scoped NNReal

theorem CurrentContinuousF {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : MetricCurrent1 E)
    (f : E → ℝ) (bF : ℝ≥0) (hbF : ∀ x, |f x| ≤ (bF : ℝ)) (LF : ℝ≥0) (hLF : LipschitzWith LF f)
    (pi : E → ℝ) (Lpi : ℝ≥0) (hLpi : LipschitzWith Lpi pi)
    (fs : ℕ → E → ℝ) (bs : ℕ → ℝ≥0) (hbs : ∀ n x, |fs n x| ≤ (bs n : ℝ))
    (Ls : ℕ → ℝ≥0) (hLs : ∀ n, LipschitzWith (Ls n) (fs n))
    (b0 : ℝ≥0) (hbound : ∀ n, bs n ≤ b0)
    (hconv : ∀ x, Tendsto (fun n => fs n x) atTop (nhds (f x))) :
    Tendsto (fun n => T.toFun ⟨fs n, bs n, hbs n, Ls n, hLs n, pi, Lpi, hLpi⟩) atTop
      (nhds (T.toFun ⟨f, bF, hbF, LF, hLF, pi, Lpi, hLpi⟩)) := by sorry
