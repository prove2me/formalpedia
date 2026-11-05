-- Prove2me | Theorems.Thm_ClauseBound_Rec_Tail_two_point_le
-- name    : ClauseBound.Rec.Tail.two_point_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:08.377426+00:00
-- url     : https://prove2.me/theorems/37296be5-6f4a-42ba-ae3d-ea7256e55128
-- title:
--   Tail: two point le
-- statement:
--   Hoeffding's lemma on two points: p·e^{θ(1−p)} + (1−p)·e^{−θp} ≤ e^{θ²/8} for 0 ≤ p ≤ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Tail.lean#L30-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Tail.lean#L30-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_ClauseBound_Rec_Tail
set_option autoImplicit false
section
section
open Finset
open ClauseBound ClauseBound.Rec
open ClauseBound.Rec.Tail

theorem ClauseBound.Rec.Tail.two_point_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    p * Real.exp (θ * (1 - p)) + (1 - p) * Real.exp (θ * (0 - p)) ≤ Real.exp (θ ^ 2 / 8) := by sorry
