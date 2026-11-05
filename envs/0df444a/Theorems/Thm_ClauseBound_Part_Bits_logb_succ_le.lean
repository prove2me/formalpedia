-- Prove2me | Theorems.Thm_ClauseBound_Part_Bits_logb_succ_le
-- name    : ClauseBound.Part.Bits.logb_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:56.997749+00:00
-- url     : https://prove2.me/theorems/32c42bb7-9ddb-4254-a5b8-f74878eb67e9
-- title:
--   Bits: logb succ le
-- statement:
--   log₂(k·h + 1) ≤ 3 + log₂ h for k ≤ 4 and h ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bits.lean#L191-L199
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bits.lean#L191-L199

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
import Definitions.Def_ClauseBound_Part_Bits
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part ClauseBound.Part.Bits
open Finset Partitions Real

theorem ClauseBound.Part.Bits.logb_succ_le {k h : ℕ} (hk : k ≤ 4) (hh : 1 ≤ h) : logb 2 ((k * h + 1 : ℕ) : ℝ) ≤ 3 + logb 2 h := by sorry
