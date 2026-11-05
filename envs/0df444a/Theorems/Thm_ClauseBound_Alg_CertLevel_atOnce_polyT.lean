-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_atOnce_polyT
-- name    : ClauseBound.Alg.CertLevel.atOnce_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:01:36.238222+00:00
-- url     : https://prove2.me/theorems/de0ef59f-13e6-4ae2-8018-c29a5de8acd0
-- title:
--   Cert Level: at Once poly T
-- statement:
--   Is the term of a pattern evaluated at once?
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L188-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L188-L190

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
variable (hP : P.Keeps)
include hP

theorem ClauseBound.Alg.CertLevel.atOnce_polyT {s : α → Step} {l : α → U} {y : α → ℕ} (hs : PolyT s) (hl : PolyT l) (hy : PolyT y) :
    PolyT fun x => ((s x).thin && colSide P (s x) (l x).length (y x)) := by sorry
