-- Prove2me | Theorems.Thm_ClauseBound_Alg_Decode_clauses_polyT
-- name    : ClauseBound.Alg.Decode.clauses_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:28:12.077694+00:00
-- url     : https://prove2.me/theorems/f7e1a8c0-914d-48e5-8fc6-fe31053203f6
-- title:
--   Decode: clauses poly T
-- statement:
--   Reading the list of clauses from the body b, one block of k·w bits per clause, is
--   polynomial-time, k in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean#L58-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean#L58-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_Alg_Decode
import Theorems.Thm_Groundwork_DecodeK_clauses_polyT
import Theorems.Thm_Groundwork_Decode_clauses_polyT
import Theorems.Thm_Groundwork_Decode_width_polyT
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.Decode.width_polyT
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Decode
open Groundwork CountKSat
open Groundwork.Decode (slotDec width width_polyT)
open Groundwork.DecodeK (clauseDec decK)
variable {α : Type} [Enc α]

theorem ClauseBound.Alg.Decode.clauses_polyT {k w : α → ℕ} {b : α → List Bool} (hk : Unary k) (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => ((List.range (b x).length).take ((b x).length / (k x * w x))).map fun c =>
      clauseDec (k x) (w x) (block (k x * w x) c (b x)) := by sorry
