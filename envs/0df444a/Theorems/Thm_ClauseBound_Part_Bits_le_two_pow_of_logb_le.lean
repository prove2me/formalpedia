-- Prove2me | Theorems.Thm_ClauseBound_Part_Bits_le_two_pow_of_logb_le
-- name    : ClauseBound.Part.Bits.le_two_pow_of_logb_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:49.375199+00:00
-- url     : https://prove2.me/theorems/e0602005-a290-4abc-9c20-ac25bb7468aa
-- title:
--   Bits: le two pow of logb le
-- statement:
--   If log₂ r ≤ y ≤ c then r ≤ 2^c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bits.lean#L177-L181
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bits.lean#L177-L181

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

theorem ClauseBound.Part.Bits.le_two_pow_of_logb_le {r c : ℕ} (hr : 1 ≤ r) {y : ℝ} (h1 : logb 2 r ≤ y) (h2 : y ≤ c) : r ≤ 2 ^ c := by sorry
