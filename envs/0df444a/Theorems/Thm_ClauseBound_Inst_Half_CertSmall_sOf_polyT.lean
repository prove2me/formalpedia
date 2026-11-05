-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_CertSmall_sOf_polyT
-- name    : ClauseBound.Inst.Half.CertSmall.sOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:44:13.526288+00:00
-- url     : https://prove2.me/theorems/6dae92e8-0947-4d69-8131-6cef632d86d2
-- title:
--   Cert Small: s Of poly T
-- statement:
--   s = i − 2h, with i cut off at 4h, is polynomial-time in h and i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean#L27-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean#L27-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.CertSmall
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.CertSmall.sOf_polyT {h i : α → ℕ} (hh : PolyT h) (hi : PolyT i) : PolyT fun x => sOf (h x) (i x) := by sorry
