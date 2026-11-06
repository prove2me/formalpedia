-- Prove2me | Theorems.Thm_ExplicitCost_nPatterns_readyOf
-- name    : ExplicitCost.nPatterns_readyOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:20:24.957607+00:00
-- url     : https://prove2.me/theorems/670b12d3-4a31-46ef-bc2d-443cd4c3a7a8
-- title:
--   Explicit Cost: n Patterns ready Of
-- statement:
--   The number of patterns is |𝓘|^{|ℛ|}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L56-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L56-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ}

theorem ExplicitCost.nPatterns_readyOf (hl : hLev h = l + 1) : nPatterns (readyOf D x₀ h) = #(D.fam (hLam h)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := by sorry
