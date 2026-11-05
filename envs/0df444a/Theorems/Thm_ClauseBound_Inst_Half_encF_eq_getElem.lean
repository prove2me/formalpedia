-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_encF_eq_getElem
-- name    : ClauseBound.Inst.Half.encF_eq_getElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:52:14.286992+00:00
-- url     : https://prove2.me/theorems/4d5e5d52-d89e-4ec5-b7de-23b1777c1533
-- title:
--   Half: enc F eq get Elem
-- statement:
--   The partition of a string is the entry at that position.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L46-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L46-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}

theorem ClauseBound.Inst.Half.encF_eq_getElem (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    encF (allTab W) h (bitsOf x) = ((allTab W).getD h [])[ofWord (bitsOf x)]'(ofWord_bitsOf_lt_length hW hp x) := by sorry
