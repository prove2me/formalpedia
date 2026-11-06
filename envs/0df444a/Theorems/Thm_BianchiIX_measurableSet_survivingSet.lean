-- Prove2me | Theorems.Thm_BianchiIX_measurableSet_survivingSet
-- name    : BianchiIX.measurableSet_survivingSet
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T16:59:27.669327+00:00
-- url     : https://prove2.me/theorems/c0005b44-d3f1-4c80-a779-527056937672
-- title:
--   Measurability of the surviving set
-- statement:
--   For a sequence of sets $K_n$ in a space $X$, define
--   $$K_\infty=\bigcap_{n\geq0}K_n,\qquad F_n=K_n\setminus K_{n+1}.$$
--   For real maps $H_i$ and sets $A_i\subset\mathbb R$, put
--   $$\mathcal S(H,A)=\bigcup_i H_i(A_i).$$
--   In a measurable space $X$, if every $K_n$ is
--   measurable, then $K_\infty$ is measurable.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/StoppedMass.lean#L186-L188

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

theorem BianchiIX.measurableSet_survivingSet {X : Type*} [MeasurableSpace X]
    (K : ℕ → Set X) (hK : ∀ m, MeasurableSet (K m)) : MeasurableSet (survivingSet K) := by sorry
