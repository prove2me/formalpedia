-- Prove2me | Theorems.Thm_BianchiIX_gaussWeight_inverse_jacobian
-- name    : BianchiIX.gaussWeight_inverse_jacobian
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:37:03.343175+00:00
-- url     : https://prove2.me/theorems/936d860d-f656-45ce-88b9-83c556c5a7ff
-- title:
--   Gauss density times an inverse-branch Jacobian
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   Let $T(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$, with $T(0)=0$.
--   For $b\geq1$, write $g_b(x)=1/(b+x)$, using the total reciprocal $0^{-1}=0$.
--   For real $b\geq1$ and $x\geq0$,
--   $$w(g_b(x))|g_b'(x)|=\frac1{\log2}\left(\frac1{b+x}-\frac1{b+1+x}\right).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussTransfer.lean#L10-L18

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

theorem BianchiIX.gaussWeight_inverse_jacobian {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) :
    gaussWeight (gaussInv a x) * |deriv (gaussInv a) x| =
      (1 / Real.log 2) * (1 / (a + x) - 1 / (a + 1 + x)) := by sorry
