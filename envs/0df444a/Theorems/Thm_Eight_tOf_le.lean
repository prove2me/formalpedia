-- Prove2me | Theorems.Thm_Eight_tOf_le
-- name    : Eight.tOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:22.859923+00:00
-- url     : https://prove2.me/theorems/72835c33-7432-4cb1-b72c-2023d8831653
-- title:
--   Eight: t Of le
-- statement:
--   t = ⌈λ/3⌉ ≤ λ for λ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/App_Pieces.lean#L27-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/App_Pieces.lean#L27-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_App_Pieces
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.tOf_le {lam : ℕ} (hl : 1 ≤ lam) : tOf lam ≤ lam := by sorry
