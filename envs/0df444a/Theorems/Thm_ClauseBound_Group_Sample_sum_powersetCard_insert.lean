-- Prove2me | Theorems.Thm_ClauseBound_Group_Sample_sum_powersetCard_insert
-- name    : ClauseBound.Group.Sample.sum_powersetCard_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:27.974888+00:00
-- url     : https://prove2.me/theorems/a3240b2f-5a58-45b7-88eb-4270da31b886
-- title:
--   Sample: sum powerset Card insert
-- statement:
--   The sum of the products over the (k+1)-subsets when one element is added.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Sample.lean#L68-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Sample.lean#L68-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Group_Sample
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
variable {ι : Type} [DecidableEq ι]
open ClauseBound.Group.Sample

theorem ClauseBound.Group.Sample.sum_powersetCard_insert {a : ι} {s : Finset ι} (ha : a ∉ s) (x : ι → ℝ) (k : ℕ) :
    ∑ S ∈ powersetCard (k + 1) (insert a s), ∏ i ∈ S, x i =
      ∑ S ∈ powersetCard (k + 1) s, ∏ i ∈ S, x i + x a * ∑ S ∈ powersetCard k s, ∏ i ∈ S, x i := by sorry
