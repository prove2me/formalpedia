-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_thin_polyT
-- name    : ClauseBound.Alg.CertGridG.thin_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:16:46.192222+00:00
-- url     : https://prove2.me/theorems/096b43c7-b296-4c5e-a86c-1a6016a52c6f
-- title:
--   Cert Grid G: thin poly T
-- statement:
--   The flag «thin» is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L261-L261
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L261-L261

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
variable {s : α → Step} (hs : PolyT s)
include hs

theorem ClauseBound.Alg.CertGridG.thin_polyT : PolyT fun x => (s x).thin := by sorry
