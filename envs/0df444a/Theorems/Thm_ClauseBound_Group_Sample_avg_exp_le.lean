-- Prove2me | Theorems.Thm_ClauseBound_Group_Sample_avg_exp_le
-- name    : ClauseBound.Group.Sample.avg_exp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:16.424214+00:00
-- url     : https://prove2.me/theorems/e5a3247a-98d4-44cd-8b62-2daced546fdd
-- title:
--   Sample: avg exp le
-- statement:
--   The mean of e^{θ c_i} is at most exp(θ·mean + (θR)²/8) if all c_i lie in [0, R].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Sample.lean#L133-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Sample.lean#L133-L170

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
omit [DecidableEq ι]

theorem ClauseBound.Group.Sample.avg_exp_le (s : Finset ι) (c : ι → ℝ) {R : ℝ} (hR : 0 < R) (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ R) (hs : s.Nonempty) (θ : ℝ) :
    (∑ i ∈ s, Real.exp (θ * c i)) / #s ≤ Real.exp (θ * ((∑ i ∈ s, c i) / #s) + (θ * R) ^ 2 / 8) := by sorry
