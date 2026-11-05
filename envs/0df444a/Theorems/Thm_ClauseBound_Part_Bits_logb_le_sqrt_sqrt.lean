-- Prove2me | Theorems.Thm_ClauseBound_Part_Bits_logb_le_sqrt_sqrt
-- name    : ClauseBound.Part.Bits.logb_le_sqrt_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:57.76919+00:00
-- url     : https://prove2.me/theorems/3da193bf-2e02-4304-9718-a11b36557186
-- title:
--   Bits: logb le sqrt sqrt
-- statement:
--   log₂ E ≤ 4·E^(1/4)/ln 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bits.lean#L151-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bits.lean#L151-L162

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

theorem ClauseBound.Part.Bits.logb_le_sqrt_sqrt {E : ℕ} (hE : 1 ≤ E) : logb 2 E ≤ 4 * √√(E : ℝ) / Real.log 2 := by sorry
