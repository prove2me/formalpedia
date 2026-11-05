-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_thin_polyT
-- name    : ClauseBound.Alg.CertLevel.thin_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:11:04.886073+00:00
-- url     : https://prove2.me/theorems/e7eeb0b0-4f29-4597-bea8-7f2bf6b25490
-- title:
--   Cert Level: thin poly T
-- statement:
--   The Cert Level construction uses the thin poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L73-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L73-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.thin_polyT {s : α → Step} (hs : PolyT s) : PolyT fun x => (s x).thin := by sorry
