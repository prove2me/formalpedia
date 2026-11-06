-- Prove2me | Theorems.Thm_BianchiIX_root_sdiff_survivingSet
-- name    : BianchiIX.root_sdiff_survivingSet
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T17:00:15.354018+00:00
-- url     : https://prove2.me/theorems/7bde6351-dec1-4379-81f5-257e22aaf1cf
-- title:
--   Decomposition of lost points by their first stopping time
-- statement:
--   For a sequence of sets $K_n$ in a space $X$, define
--   $$K_\infty=\bigcap_{n\geq0}K_n,\qquad F_n=K_n\setminus K_{n+1}.$$
--   For real maps $H_i$ and sets $A_i\subset\mathbb R$, put
--   $$\mathcal S(H,A)=\bigcup_i H_i(A_i).$$
--   If $K_{n+1}\subset K_n$ for every $n$, then
--   $$K_0\setminus K_\infty=\bigcup_{n\geq0}F_n.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/StoppedMass.lean#L194-L211

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

theorem BianchiIX.root_sdiff_survivingSet {X : Type*} (K : ℕ → Set X) (hK : Antitone K) :
    K 0 \ survivingSet K = ⋃ m, firstStoppedSet K m := by sorry
