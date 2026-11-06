-- Prove2me | Theorems.Thm_BianchiIX_invariant_set_volume_zero_or_compl_zero
-- name    : BianchiIX.invariant_set_volume_zero_or_compl_zero
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:48:23.516565+00:00
-- url     : https://prove2.me/theorems/7c5f7587-e562-4b84-ad11-c1877b51277d
-- title:
--   Invariant sets have zero or full phase length
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   Let $T(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$, with $T(0)=0$.
--   For $b\geq1$, write $g_b(x)=1/(b+x)$, using the total reciprocal $0^{-1}=0$.
--   If $E$ is Borel and $T^{-1}(E)=E$, then
--   $$\lambda_0(E)=0\quad\text{or}\quad\lambda_0(E^c)=0.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussErgodic.lean#L60-L78

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
import Mathlib.Dynamics.Ergodic.Ergodic

open Set Filter MeasureTheory
open scoped ENNReal
open BianchiIX

theorem BianchiIX.invariant_set_volume_zero_or_compl_zero {E : Set ℝ} (hE : MeasurableSet E)
    (hinv : gaussMap ⁻¹' E = E) :
    (volume.restrict (Ioo (0 : ℝ) 1)) E = 0 ∨
      (volume.restrict (Ioo (0 : ℝ) 1)) Eᶜ = 0 := by sorry
