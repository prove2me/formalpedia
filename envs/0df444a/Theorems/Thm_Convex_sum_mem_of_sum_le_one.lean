-- Prove2me | Theorems.Thm_Convex_sum_mem_of_sum_le_one
-- name    : Convex.sum_mem_of_sum_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:30:44.496579+00:00
-- url     : https://prove2.me/theorems/df9b9f7b-c7a7-4532-bfb3-0ba8b85a04bd
-- title:
--   MarkovProcess: sum_mem_of_sum_le_one
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Generation_6c19e644
import Definitions.Def_MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Invariant sets and strong semigroup limits

This file isolates the topological part of transferring an invariant set from
bounded Yosida approximations to the generated semigroup.  It also records the
finite-iterate consequence of invariance under a normalized resolvent.  The
Poisson-series argument transferring the latter invariance to each exponential
approximant is in `Semigroup/PoissonInvariant.lean`.
-/

open Filter Set Topology

noncomputable section

namespace MarkovProcess.Semigroup



namespace PreservesSet

variable {E F G : Type*} {C : Set E} {D : Set F} {K : Set G}







end PreservesSet

end MarkovProcess.Semigroup

namespace Convex

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end Convex

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



section CompleteSpace

variable [CompleteSpace E]





end CompleteSpace

end ContractiveResolvent

end MarkovProcess.Semigroup


open Convex
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Invariant sets and strong semigroup limits

This file isolates the topological part of transferring an invariant set from
bounded Yosida approximations to the generated semigroup.  It also records the
finite-iterate consequence of invariance under a normalized resolvent.  The
Poisson-series argument transferring the latter invariance to each exponential
approximant is in `Semigroup/PoissonInvariant.lean`.
-/

open Filter Set Topology




variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Convex in

theorem Convex.sum_mem_of_sum_le_one {C : Set E} (hC : Convex ℝ C) (hzero : 0 ∈ C)
    (s : Finset ι) (w : ι → ℝ) (z : ι → E)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i ≤ 1)
    (hz : ∀ i ∈ s, z i ∈ C) :
    ∑ i ∈ s, w i • z i ∈ C := by sorry
