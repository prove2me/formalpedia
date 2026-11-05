-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_dig_polyT
-- name    : ClauseBound.Alg.CertLevel.dig_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:17:55.741588+00:00
-- url     : https://prove2.me/theorems/9cc5ae32-6852-4d8a-8f7a-82425794a67c
-- title:
--   Cert Level: dig poly T
-- statement:
--   A digit of a pattern.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L113-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L113-L116

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

theorem ClauseBound.Alg.CertLevel.dig_polyT {s : α → Step} {l : α → U} {y q : α → ℕ} (hs : PolyT s) (hl : PolyT l) (hy : PolyT y) (hq : PolyT q) :
    PolyT fun x => digit (P.cnt (s x).h (l x).length - 1) (y x) (q x) := by sorry
