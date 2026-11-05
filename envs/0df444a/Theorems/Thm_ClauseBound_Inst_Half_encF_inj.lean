-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_encF_inj
-- name    : ClauseBound.Inst.Half.encF_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:01.848212+00:00
-- url     : https://prove2.me/theorems/77f887c7-bd26-4131-9d68-97879c9ba56e
-- title:
--   Half: enc F inj
-- statement:
--   Different strings stand for different partitions, also as multisets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L69-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L69-L79

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

theorem ClauseBound.Inst.Half.encF_inj (hW : h ≤ W) (hp : 2 ^ lam ≤ Partitions.p h) (x v : Pieces.Bits lam)
    (e : (encF (allTab W) h (bitsOf x) : Multiset ℕ) = encF (allTab W) h (bitsOf v)) : x = v := by sorry
