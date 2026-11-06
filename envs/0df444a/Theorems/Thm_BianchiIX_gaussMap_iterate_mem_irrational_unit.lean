-- Prove2me | Theorems.Thm_BianchiIX_gaussMap_iterate_mem_irrational_unit
-- name    : BianchiIX.gaussMap_iterate_mem_irrational_unit
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:43:09.735609+00:00
-- url     : https://prove2.me/theorems/7e35a12a-dddc-445b-8796-6adeeb675670
-- title:
--   All iterates of an irrational phase stay in the unit interval
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   Let $T(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$, with $T(0)=0$.
--   For $b\geq1$, write $g_b(x)=1/(b+x)$, using the total reciprocal $0^{-1}=0$.
--   For irrational $x\in(0,1)$ and every integer $n\geq0$,
--   $T^n(x)$ is irrational and belongs to $(0,1)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussComplete.lean#L10-L17

import Definitions.Def_BianchiIX_Statistics_GaussCoding
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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX

theorem BianchiIX.gaussMap_iterate_mem_irrational_unit {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hi : Irrational x) (n : ℕ) :
    gaussMap^[n] x ∈ Ioo (0 : ℝ) 1 ∧ Irrational (gaussMap^[n] x) := by sorry
