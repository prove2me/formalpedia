-- Prove2me | Theorems.Thm_ClauseBound_Group_card_sample_tail_le
-- name    : ClauseBound.Group.card_sample_tail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:26.537889+00:00
-- url     : https://prove2.me/theorems/53c3c915-c651-494d-a7df-f07f275bf8ba
-- title:
--   Group: card sample tail le
-- statement:
--   Among the n-subsets S of s, at most the fraction exp(−2nt²) has Σ_{i ∈ S} c_i ≥ n·(mean of c) +
--   t·n·R, if all c_i lie in [0, R].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Sample.lean#L178-L212
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Sample.lean#L178-L212

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
open Sample

theorem ClauseBound.Group.card_sample_tail_le (s : Finset ι) (c : ι → ℝ) {R t : ℝ} (hR : 0 < R) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ R) (hs : s.Nonempty)
    (n : ℕ) (ht : 0 ≤ t) :
    (#{S ∈ powersetCard n s | n * ((∑ i ∈ s, c i) / #s) + t * n * R ≤ ∑ i ∈ S, c i} : ℝ)
      ≤ Real.exp (-(2 * n * t ^ 2)) * ((#s).choose n : ℝ) := by sorry
