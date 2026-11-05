-- Prove2me | Theorems.Thm_ClauseBound_Alg_Decode_clauseDec_polyT
-- name    : ClauseBound.Alg.Decode.clauseDec_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:08.973133+00:00
-- url     : https://prove2.me/theorems/ea1c77c5-d044-4a00-a616-5f88ea3d8ab5
-- title:
--   Decode: clause Dec poly T
-- statement:
--   Reading one clause from a block of k slots of w bits is polynomial-time, k in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean#L51-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean#L51-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_Alg_Decode
import Theorems.Thm_Groundwork_DecodeK_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_clauseDec_polyT
import Theorems.Thm_Groundwork_Decode_width_polyT
attribute [local fun_prop] Groundwork.Decode.clauseDec_polyT
attribute [local fun_prop] Groundwork.Decode.width_polyT
attribute [local fun_prop] Groundwork.DecodeK.clauseDec_polyT


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Decode
open Groundwork CountKSat
open Groundwork.Decode (slotDec width width_polyT)
open Groundwork.DecodeK (clauseDec decK)
variable {α : Type} [Enc α]

theorem ClauseBound.Alg.Decode.clauseDec_polyT {k w : α → ℕ} {b : α → List Bool} (hk : Unary k) (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => clauseDec (k x) (w x) (b x) := by sorry
