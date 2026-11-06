-- Prove2me | Theorems.Thm_BianchiIX_measurable_birkhoffAverage
-- name    : BianchiIX.measurable_birkhoffAverage
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T18:24:53.808268+00:00
-- url     : https://prove2.me/theorems/fd335f45-e06c-46cc-9a74-bd0005b03af9
-- title:
--   Measurability of each finite Birkhoff average
-- statement:
--   Let $F:X\to X$, let $(f_i:X\to\mathbb R)_{i\in I}$
--   be a family of observables, and let $l_i\in\mathbb R$. Define
--   $$A_n^Ff(x)=\frac1n\sum_{j=0}^{n-1}f(F^jx)\quad(n\geq1),\qquad A_0^Ff(x)=0,$$
--   $$\mathcal B(F,f,l)=\{x\in X:\ \forall i\in I,\ A_n^Ff_i(x)\longrightarrow l_i\}.$$
--
--   Give $X$ a sigma algebra. If $F$ and a real observable $h$ are measurable,
--   then $x\mapsto A_n^Fh(x)$ is measurable for every $n\geq0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/CommonTypical.lean#L14-L18

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

theorem BianchiIX.measurable_birkhoffAverage {X : Type*} [MeasurableSpace X] {F : X → X} {f : X → ℝ}
    (hF : Measurable F) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffAverage ℝ F f n) := by sorry
