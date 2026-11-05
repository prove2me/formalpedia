-- Prove2me | Theorems.Thm_ClauseBound_Part_mem_partsLe
-- name    : ClauseBound.Part.mem_partsLe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:36:26.71521+00:00
-- url     : https://prove2.me/theorems/c7304b7f-dac8-4c91-87f9-260d120b4182
-- title:
--   Part: mem parts Le
-- statement:
--   The members of `partsLe E k`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean#L62-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean#L62-L116

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

theorem ClauseBound.Part.mem_partsLe (E k : ℕ) (L : List ℕ) :
    L ∈ partsLe E k ↔ L.sum = E ∧ (∀ n ∈ L, 1 ≤ n ∧ n ≤ k) ∧ L.Pairwise (· ≥ ·) := by sorry
