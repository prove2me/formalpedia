-- Prove2me | Theorems.Thm_ClauseBound_Part_ListP_length_partsLe_aux
-- name    : ClauseBound.Part.ListP.length_partsLe_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:26:22.61158+00:00
-- url     : https://prove2.me/theorems/97eef9fe-1cd6-4dee-9b04-6c69c3af2f19
-- title:
--   List P: length parts Le aux
-- statement:
--   For E ≥ 1 there are at most 2^E − 2^(E−k) lists; for E = 0 there is one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean#L176-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean#L176-L197

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
open ClauseBound.Part.ListP

theorem ClauseBound.Part.ListP.length_partsLe_aux (E k : ℕ) : (partsLe E k).length ≤ 2 ^ E ∧ (1 ≤ E → (partsLe E k).length + 2 ^ (E - k) ≤ 2 ^ E) := by sorry
