-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_ofWord_bitsOf_inj
-- name    : ClauseBound.Inst.Half.ofWord_bitsOf_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:38:41.248867+00:00
-- url     : https://prove2.me/theorems/d72b1fa3-b799-4b4d-957c-486094cfaa61
-- title:
--   Half: of Word bits Of inj
-- statement:
--   Different strings write different numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L33-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L33-L37

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

theorem ClauseBound.Inst.Half.ofWord_bitsOf_inj {x v : Pieces.Bits lam} (e : ofWord (bitsOf x) = ofWord (bitsOf v)) : x = v := by sorry
