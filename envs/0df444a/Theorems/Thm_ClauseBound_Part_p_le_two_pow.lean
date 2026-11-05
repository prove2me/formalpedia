-- Prove2me | Theorems.Thm_ClauseBound_Part_p_le_two_pow
-- name    : ClauseBound.Part.p_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:27:03.175818+00:00
-- url     : https://prove2.me/theorems/0efa485b-4631-40d7-ae50-7fb3c7cfc1c7
-- title:
--   Part: p le two pow
-- statement:
--   p(E) ≤ 2^E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean#L255-L257
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean#L255-L257

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
import Definitions.Def_ClauseBound_Part_ListP
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ListP

theorem ClauseBound.Part.p_le_two_pow (E : ℕ) : Partitions.p E ≤ 2 ^ E := by sorry
