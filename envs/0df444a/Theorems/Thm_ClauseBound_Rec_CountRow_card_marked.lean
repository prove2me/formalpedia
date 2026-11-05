-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_card_marked
-- name    : ClauseBound.Rec.CountRow.card_marked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:18.556402+00:00
-- url     : https://prove2.me/theorems/574f7b9f-135b-4d46-827c-9ae8f0b2c579
-- title:
--   Count Row: card marked
-- statement:
--   The share of the choices that are marked at the place b is |S b|/|Ω b|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L38-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L38-L51

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

theorem ClauseBound.Rec.CountRow.card_marked (b : Fin δ) :
    (#{ω : ∀ b, Ω b | ω b ∈ S b} : ℝ) = (Fintype.card (∀ b, Ω b) : ℝ) * ((#(S b) : ℝ) / Fintype.card (Ω b)) := by sorry
