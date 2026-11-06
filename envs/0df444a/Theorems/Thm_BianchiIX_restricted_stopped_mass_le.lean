-- Prove2me | Theorems.Thm_BianchiIX_restricted_stopped_mass_le
-- name    : BianchiIX.restricted_stopped_mass_le
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:59:00.254424+00:00
-- url     : https://prove2.me/theorems/ca1641ab-9fd3-4522-9735-09cbe1b68876
-- title:
--   Restricting a stopping-loss bound
-- statement:
--   Let $I,F\subset\mathbb R$ and $B\in[0,\infty]$. If
--   $\lambda(F)\leq B$, then
--   $$\lambda(I\cap F)\leq\min\{\lambda(I),B\}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/StoppedMass.lean#L178-L180

import Definitions.Def_BianchiIX_Statistics_StoppedMass
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

open BianchiIX
noncomputable section
open Set MeasureTheory
open scoped ENNReal

theorem BianchiIX.restricted_stopped_mass_le {I F : Set ℝ} {B : ℝ≥0∞} (hF : volume F ≤ B) :
    volume (I ∩ F) ≤ min (volume I) B := by sorry
