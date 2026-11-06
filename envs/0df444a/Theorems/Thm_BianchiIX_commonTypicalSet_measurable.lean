-- Prove2me | Theorems.Thm_BianchiIX_commonTypicalSet_measurable
-- name    : BianchiIX.commonTypicalSet_measurable
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T18:31:57.970502+00:00
-- url     : https://prove2.me/theorems/13197a06-78ee-47a8-bac5-6be69ec39da9
-- title:
--   Measurability of the common typical set
-- statement:
--   Let $F:X\to X$, let $(f_i:X\to\mathbb R)_{i\in I}$
--   be a family of observables, and let $l_i\in\mathbb R$. Define
--   $$A_n^Ff(x)=\frac1n\sum_{j=0}^{n-1}f(F^jx)\quad(n\geq1),\qquad A_0^Ff(x)=0,$$
--   $$\mathcal B(F,f,l)=\{x\in X:\ \forall i\in I,\ A_n^Ff_i(x)\longrightarrow l_i\}.$$
--
--   Suppose $X$ is a measurable space, $I$ is countable, and $F$ and every
--   $f_i$ are measurable. Then $\mathcal B(F,f,l)$ is measurable.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/CommonTypical.lean#L20-L25

import Definitions.Def_BianchiIX_Statistics_CommonTypical
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
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX

theorem BianchiIX.commonTypicalSet_measurable {X ι : Type*} [MeasurableSpace X] [Countable ι]
    {F : X → X} {f : ι → X → ℝ} (l : ι → ℝ)
    (hF : Measurable F) (hf : ∀ i, Measurable (f i)) : MeasurableSet (commonTypicalSet F f l) := by sorry
