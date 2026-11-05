-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_prod_sg
-- name    : ClauseBound.Rec.CountRow.prod_sg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:22.29029+00:00
-- url     : https://prove2.me/theorems/236677bc-4bad-4ced-a1e9-74cfff5d5405
-- title:
--   Count Row: prod sg
-- statement:
--   The product of the signs of a label is −1 if the number of entries 11 is odd, and 1 otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L67-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L67-L76

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

theorem ClauseBound.Rec.CountRow.prod_sg {ι : Type} [Fintype ι] (γ : ι → Bool × Bool) :
    ∏ k, sg (γ k) = if Odd #{k | γ k = (true, true)} then -1 else 1 := by sorry
