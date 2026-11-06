-- Prove2me | Theorems.Thm_Eight_Width_cntN_splitN
-- name    : Eight.Width.cntN_splitN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:01:03.011394+00:00
-- url     : https://prove2.me/theorems/576d2209-ca42-408a-b348-33f5d0f35e33
-- title:
--   Width: cnt N split N
-- statement:
--   The number of satisfying assignments in the form of the counting programs of this development:
--   on the formula of an instance, the program keeps it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L155-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L155-L157

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Width
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_WidthProg
set_option autoImplicit false
section
section
open Eight Eight.Width
open Groundwork Groundwork.Prog CountKSat

theorem Eight.Width.cntN_splitN {n : ℕ} (φ : Sat3.CNF n) :
    cntN (n + numFresh (Decode.toN φ)) (splitN n (Decode.toN φ)) = cntN n (Decode.toN φ) := by sorry
