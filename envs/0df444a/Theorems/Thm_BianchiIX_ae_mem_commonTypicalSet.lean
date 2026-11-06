-- Prove2me | Theorems.Thm_BianchiIX_ae_mem_commonTypicalSet
-- name    : BianchiIX.ae_mem_commonTypicalSet
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T18:25:58.749026+00:00
-- url     : https://prove2.me/theorems/ae05596b-c564-46b8-a4de-67653f5adde3
-- title:
--   A common full-measure set for countably many averaging limits
-- statement:
--   Let $F:X\to X$, let $(f_i:X\to\mathbb R)_{i\in I}$
--   be a family of observables, and let $l_i\in\mathbb R$. Define
--   $$A_n^Ff(x)=\frac1n\sum_{j=0}^{n-1}f(F^jx)\quad(n\geq1),\qquad A_0^Ff(x)=0,$$
--   $$\mathcal B(F,f,l)=\{x\in X:\ \forall i\in I,\ A_n^Ff_i(x)\longrightarrow l_i\}.$$
--
--   Let $\mu$ be a measure on $X$ and let $I$ be countable. If for every $i$
--   the limit $A_n^Ff_i(x)\to l_i$ holds for $\mu$-almost every $x$, then
--   $$x\in\mathcal B(F,f,l)\quad\text{for }\mu\text{-almost every }x.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/CommonTypical.lean#L27-L31

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

theorem BianchiIX.ae_mem_commonTypicalSet {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (F : X → X) (f : ι → X → ℝ) (l : ι → ℝ)
    (h : ∀ i, ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ F (f i) n x) atTop (𝓝 (l i))) :
    ∀ᵐ x ∂μ, x ∈ commonTypicalSet F f l := by sorry
