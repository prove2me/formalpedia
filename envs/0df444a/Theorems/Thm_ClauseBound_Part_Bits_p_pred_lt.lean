-- Prove2me | Theorems.Thm_ClauseBound_Part_Bits_p_pred_lt
-- name    : ClauseBound.Part.Bits.p_pred_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:16:46.585867+00:00
-- url     : https://prove2.me/theorems/85ce91b6-5a61-4c84-9592-b86deabfa8d2
-- title:
--   Bits: p pred lt
-- statement:
--   p(h − 1) < 2^λ, because h is the least.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bits.lean#L140-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bits.lean#L140-L148

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

theorem ClauseBound.Part.Bits.p_pred_lt {lam : ℕ} (hl : 1 ≤ lam) : p (hOf lam - 1) < 2 ^ lam := by sorry
