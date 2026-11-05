-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_Nof_polyT
-- name    : ClauseBound.Alg.CertLevel.Nof_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:04:03.519975+00:00
-- url     : https://prove2.me/theorems/1dcafc24-af23-4745-be55-dbb573833f5a
-- title:
--   Cert Level: Nof poly T
-- statement:
--   N = (pd)²λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L357-L363
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L357-L363

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

theorem ClauseBound.Alg.CertLevel.Nof_polyT {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => Nof (s x) (l x).length := by sorry
