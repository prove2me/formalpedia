-- Prove2me | Theorems.Thm_ClauseBound_Group_Sample_esymm_le
-- name    : ClauseBound.Group.Sample.esymm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:24.966617+00:00
-- url     : https://prove2.me/theorems/8cca031c-b280-49cd-8776-9c1cc7c22751
-- title:
--   Sample: esymm le
-- statement:
--   The sum of the products over the n-subsets is at most C(N, n) times the n-th power of the mean.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Sample.lean#L85-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Sample.lean#L85-L129

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

theorem ClauseBound.Group.Sample.esymm_le (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∀ n : ℕ, ∑ S ∈ powersetCard n s, ∏ i ∈ S, x i ≤ ((#s).choose n : ℝ) * ((∑ i ∈ s, x i) / #s) ^ n := by sorry
