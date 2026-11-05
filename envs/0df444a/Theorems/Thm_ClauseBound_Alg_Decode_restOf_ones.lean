-- Prove2me | Theorems.Thm_ClauseBound_Alg_Decode_restOf_ones
-- name    : ClauseBound.Alg.Decode.restOf_ones
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:39:05.288076+00:00
-- url     : https://prove2.me/theorems/98f88bb2-1460-487f-8695-976478e780ec
-- title:
--   Decode: rest Of ones
-- statement:
--   `restOf` reads w from 1ᵏ 0 w.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean#L36-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean#L36-L37

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

theorem ClauseBound.Alg.Decode.restOf_ones (k : ℕ) (w : List Bool) : restOf (List.replicate k true ++ false :: w) = w := by sorry
