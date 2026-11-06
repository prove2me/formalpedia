-- Prove2me | Theorems.Thm_BianchiIX_gaussMeasure_inverse_sum
-- name    : BianchiIX.gaussMeasure_inverse_sum
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:45:39.941475+00:00
-- url     : https://prove2.me/theorems/9b3a653c-77f7-4516-8f3d-5042f5895f2a
-- title:
--   Sum of Gauss measures over inverse branches
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   Let $T(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$, with $T(0)=0$.
--   For $b\geq1$, write $g_b(x)=1/(b+x)$, using the total reciprocal $0^{-1}=0$.
--   For every Borel $A\subset(0,1)$,
--   $$\sum_{j=0}^{\infty}\mu_G(g_{j+1}(A))=\mu_G(A).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussTransfer.lean#L72-L92

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX

theorem BianchiIX.gaussMeasure_inverse_sum {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    (∑' j : ℕ, gaussMeasure (gaussInv ((j : ℝ) + 1) '' A)) = gaussMeasure A := by sorry
