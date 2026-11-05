-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_ebarG_polyT
-- name    : ClauseBound.Alg.CertLevel.ebarG_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:03:37.794123+00:00
-- url     : https://prove2.me/theorems/0cda621b-e40b-4bdf-b625-84ad9cacdb1e
-- title:
--   Cert Level: ebar G poly T
-- statement:
--   The bound for the column networks that are evaluated by enumeration.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L296-L309
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L296-L309

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

theorem ClauseBound.Alg.CertLevel.ebarG_polyT {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => ebarG (s x) (l x).length := by sorry
