-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_sum_marked
-- name    : ClauseBound.Rec.CountRow.sum_marked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:12.568092+00:00
-- url     : https://prove2.me/theorems/4cc9d409-38c2-4bac-90bf-f4c6cc201065
-- title:
--   Count Row: sum marked
-- statement:
--   The sum of the number of marked places over all choices is the number of choices times Σ_b |S
--   b|/|Ω b|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L55-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L55-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {δ : ℕ} (Ω : Fin δ → Type) [∀ b, Fintype (Ω b)] [∀ b, Nonempty (Ω b)] [∀ b, DecidableEq (Ω b)] (S : ∀ b, Finset (Ω b))

theorem ClauseBound.Rec.CountRow.sum_marked :
    ∑ ω : ∀ b, Ω b, (#{b | ω b ∈ S b} : ℝ) = (Fintype.card (∀ b, Ω b) : ℝ) * ∑ b, (#(S b) : ℝ) / Fintype.card (Ω b) := by sorry
