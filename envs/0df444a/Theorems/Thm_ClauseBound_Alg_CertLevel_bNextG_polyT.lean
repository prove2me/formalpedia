-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_bNextG_polyT
-- name    : ClauseBound.Alg.CertLevel.bNextG_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:04:10.286169+00:00
-- url     : https://prove2.me/theorems/9cc8cdcc-d387-4c24-b595-8c5350d5d037
-- title:
--   Cert Level: b Next G poly T
-- statement:
--   The bound for the bit length of the entries one level down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L343-L354
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L343-L354

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.bNextG_polyT (hP : P.Keeps) {s : α → Step} {l : α → U} {B : α → ℕ} (hs : PolyT s) (hl : PolyT l) (hB : PolyT B) :
    PolyT fun x => bNextG P (s x) (l x).length (B x) := by sorry
