-- Prove2me | Theorems.Thm_ClauseBound_Part_partsLe_succ
-- name    : ClauseBound.Part.partsLe_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:34.956211+00:00
-- url     : https://prove2.me/theorems/ce441e95-419b-4d71-9ebb-080934275fd4
-- title:
--   Part: parts Le succ
-- statement:
--   The step of the recursion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean#L57-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean#L57-L59

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

theorem ClauseBound.Part.partsLe_succ (E k : ℕ) :
    partsLe E (k + 1) = partsLe E k ++ (if k + 1 ≤ E then (partsLe (E - (k + 1)) (k + 1)).map fun L => (k + 1) :: L else []) := by sorry
