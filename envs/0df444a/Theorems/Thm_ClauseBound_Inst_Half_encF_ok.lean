-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_encF_ok
-- name    : ClauseBound.Inst.Half.encF_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:18.287072+00:00
-- url     : https://prove2.me/theorems/da4939d6-ed79-4ac9-8c30-0f674b3206f5
-- title:
--   Half: enc F ok
-- statement:
--   The partition of a string has positive parts and the sum h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L57-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L57-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}

theorem ClauseBound.Inst.Half.encF_ok (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x : Pieces.Bits lam) :
    ClauseBound.Boson.Pos (encF (allTab W) h (bitsOf x)) ∧ (encF (allTab W) h (bitsOf x)).sum = h := by sorry
