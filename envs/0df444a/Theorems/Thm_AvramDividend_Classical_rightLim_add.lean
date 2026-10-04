-- Prove2me | Theorems.Thm_AvramDividend_Classical_rightLim_add
-- name    : AvramDividend.Classical.rightLim_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T12:51:50.485742+00:00
-- url     : https://prove2.me/theorems/b86e3fa7-ad89-4f43-9783-9a498ce18da3
-- title:
--   Right limits commute with pointwise addition of monotone functions
-- statement:
--   For two monotone real functions $f$ and $g$, the right limit at $t$ of their pointwise sum equals the sum of their right limits at $t$.
--
--   This is the additivity counterpart of `Monotone.rightLim`, which is built on the order dual. The pinned Mathlib provides `Monotone.tendsto_nhdsGT`, giving `Tendsto f (nhdsWithin GT t) (nhds (sInf (f '' Ioi t)))`, but it provides no additivity statement for `rightLim` itself, so the fact must be established here.
--
--   The argument applies `Continuous.tendsto'` to `continuous_add` on the product filter, comparing the sum of the two individual right limits with the right limit of `f + g`. Both are limits of the same function along `nhdsWithin GT t`, and a Hausdorff topological space has a unique such limit, which is exactly `tendsto_nhds_unique`. No finiteness or sign condition on $f$, $g$ or $t$ is required.
--
--   This is a reusable ingredient for Stieltjes decompositions of paths shifted by a deterministic function on positive times: it is the step that lets `Monotone.stieltjesFunction` be compared with the sum of two Stieltjes functions, via the pinned `StieltjesFunction.measure_add`.

import Mathlib

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.rightLim_add {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) (t : ℝ) : Function.rightLim f t + Function.rightLim g t = Function.rightLim (f + g) t := by sorry
