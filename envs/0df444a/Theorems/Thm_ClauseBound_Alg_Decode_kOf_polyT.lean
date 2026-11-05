-- Prove2me | Theorems.Thm_ClauseBound_Alg_Decode_kOf_polyT
-- name    : ClauseBound.Alg.Decode.kOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:39:41.16633+00:00
-- url     : https://prove2.me/theorems/7387ff35-f7fc-4b2f-8c50-3329ce90f541
-- title:
--   Decode: k Of poly T
-- statement:
--   `kOf` is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean#L81-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean#L81-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_Alg_Decode
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

theorem ClauseBound.Alg.Decode.kOf_polyT : PolyT kOf := by sorry
