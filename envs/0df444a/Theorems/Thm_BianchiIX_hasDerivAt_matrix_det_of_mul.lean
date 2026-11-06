-- Prove2me | Theorems.Thm_BianchiIX_hasDerivAt_matrix_det_of_mul
-- name    : BianchiIX.hasDerivAt_matrix_det_of_mul
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T05:36:37.158226+00:00
-- url     : https://prove2.me/theorems/94dd3248-980e-495c-a17f-3d73ffe83939
-- title:
--   Liouville's differential identity for a matrix curve
-- statement:
--   Let $I$ be a finite index type, $A:\mathbb R\to
--   \operatorname{Mat}_{I\times I}(\mathbb R)$, and $B$ a real matrix.
--   If $A$ has derivative $BA(t)$ at $t$, then $\det A$ has derivative
--   $\operatorname{tr}(B)\det A(t)$ at $t$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/DeterminantEvolution.lean#L16-L30

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.hasDerivAt_matrix_det_of_mul {n : Type*} [Fintype n] [DecidableEq n]
    {A : ℝ → Matrix n n ℝ} {B : Matrix n n ℝ} {t : ℝ}
    (hA : HasDerivAt A (B * A t) t) :
    HasDerivAt (fun u => (A u).det) (B.trace * (A t).det) t := by sorry
