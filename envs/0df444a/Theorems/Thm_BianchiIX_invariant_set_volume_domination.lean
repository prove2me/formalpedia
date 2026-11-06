-- Prove2me | Theorems.Thm_BianchiIX_invariant_set_volume_domination
-- name    : BianchiIX.invariant_set_volume_domination
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:47:21.75131+00:00
-- url     : https://prove2.me/theorems/84af9b92-d010-4961-bb11-bd1b138d0d9d
-- title:
--   Measure domination for a Gauss-invariant set
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   Let $T(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$, with $T(0)=0$.
--   For $b\geq1$, write $g_b(x)=1/(b+x)$, using the total reciprocal $0^{-1}=0$.
--   If $E$ is Borel and $T^{-1}(E)=E$, then, as measures,
--   $$\tfrac12\lambda((0,1)\cap E)\,\lambda_0
--   \leq\lambda\mathbin{\restriction}((0,1)\cap E).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussErgodic.lean#L37-L58

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.Ergodic.Ergodic

open Set Filter MeasureTheory
open scoped ENNReal
open BianchiIX

theorem BianchiIX.invariant_set_volume_domination {E : Set ℝ} (hE : MeasurableSet E)
    (hinv : gaussMap ⁻¹' E = E) :
    ((1 / 2 : ℝ≥0∞) * volume (Ioo (0 : ℝ) 1 ∩ E)) • volume.restrict (Ioo (0 : ℝ) 1) ≤
      volume.restrict (Ioo (0 : ℝ) 1 ∩ E) := by sorry
