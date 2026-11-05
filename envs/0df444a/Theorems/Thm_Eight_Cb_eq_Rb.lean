-- Prove2me | Theorems.Thm_Eight_Cb_eq_Rb
-- name    : Eight.Cb_eq_Rb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:28.874021+00:00
-- url     : https://prove2.me/theorems/d4d99fe2-0b4c-48c5-b317-d8de230106b5
-- title:
--   Eight: Cb eq Rb
-- statement:
--   C is R with y and u exchanged; this holds by the definitions. The paper uses it in the words
--   «column-wise the roles of R and C are exchanged».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L82-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L82-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.Cb_eq_Rb (x y u v : Block) : Cb x y u v = Rb x u y v := by sorry
