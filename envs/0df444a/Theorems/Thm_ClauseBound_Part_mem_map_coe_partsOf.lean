-- Prove2me | Theorems.Thm_ClauseBound_Part_mem_map_coe_partsOf
-- name    : ClauseBound.Part.mem_map_coe_partsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:11.730118+00:00
-- url     : https://prove2.me/theorems/e2082d86-102d-4e2e-a34b-17eeda9192f6
-- title:
--   Part: mem map coe parts Of
-- statement:
--   As multisets, the members of `partsOf E` are the multisets of positive integers with sum E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean#L216-L228
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/ListP.lean#L216-L228

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

theorem ClauseBound.Part.mem_map_coe_partsOf {E : ℕ} {τ : Multiset ℕ} : τ ∈ (partsOf E).map (fun L : List ℕ => (L : Multiset ℕ)) ↔ τ.sum = E ∧ 0 ∉ τ := by sorry
