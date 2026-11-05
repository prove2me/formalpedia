-- Prove2me | Theorems.Thm_ClauseBound_Alg_Decode_decK_polyT
-- name    : ClauseBound.Alg.Decode.decK_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:28.700198+00:00
-- url     : https://prove2.me/theorems/85926905-fcbd-4250-97c2-577bb82fba17
-- title:
--   Decode: dec K poly T
-- statement:
--   The decoder `decK` is polynomial-time jointly in k, in unary, and the word.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean#L69-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean#L69-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_Alg_Decode
import Theorems.Thm_Groundwork_DecodeK_decK_polyT
import Theorems.Thm_Groundwork_Decode_width_polyT
attribute [local fun_prop] Groundwork.Decode.width_polyT


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Decode
open Groundwork CountKSat
open Groundwork.Decode (slotDec width width_polyT)
open Groundwork.DecodeK (clauseDec decK)
variable {α : Type} [Enc α]

theorem ClauseBound.Alg.Decode.decK_polyT {k : α → ℕ} {v : α → List Bool} (hk : Unary k) (hv : PolyT v) : PolyT fun x => decK (k x) (v x) := by sorry
