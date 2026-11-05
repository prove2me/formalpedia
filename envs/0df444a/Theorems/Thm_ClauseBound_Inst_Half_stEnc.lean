-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_stEnc
-- name    : ClauseBound.Inst.Half.stEnc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:18:17.072408+00:00
-- url     : https://prove2.me/theorems/c19a7d03-a363-42a1-943c-107ac361811d
-- title:
--   Half: st Enc
-- statement:
--   The encoding with the table of the partitions of 0, …, 4h, in the form in which the
--   specification of the pieces uses it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L95-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L95-L97

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

theorem ClauseBound.Inst.Half.stEnc : StEnc := by sorry
