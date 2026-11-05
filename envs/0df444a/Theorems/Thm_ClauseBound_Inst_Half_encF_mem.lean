-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_encF_mem
-- name    : ClauseBound.Inst.Half.encF_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:52:17.300877+00:00
-- url     : https://prove2.me/theorems/b69c5fcb-c163-4061-931d-d170d9c7c156
-- title:
--   Half: enc F mem
-- statement:
--   The partition of a string is in the list of the partitions of h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L51-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L51-L54

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

theorem ClauseBound.Inst.Half.encF_mem (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    encF (allTab W) h (bitsOf x) ∈ (allTab W).getD h [] := by sorry
