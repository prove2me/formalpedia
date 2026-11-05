-- Prove2me | Theorems.Thm_ClauseBound_Part_card_count_ge
-- name    : ClauseBound.Part.card_count_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:58.432526+00:00
-- url     : https://prove2.me/theorems/160d1f38-48c5-4ed3-bd12-a52719f89bcc
-- title:
--   Part: card count ge
-- statement:
--   The partitions of E in which the part v occurs at least k times are as many as the partitions of
--   E − kv.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Rec.lean#L45-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Rec.lean#L45-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_PartitionStatement
import Definitions.Def_ClauseBound_Part_Rec
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions

theorem ClauseBound.Part.card_count_ge {E v k : ℕ} (hv : 1 ≤ v) (h : k * v ≤ E) :
    #{π : Nat.Partition E | k ≤ π.parts.count v} = p (E - k * v) := by sorry
