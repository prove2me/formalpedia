-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_nParts_polyT
-- name    : ClauseBound.Alg.CertGridG.nParts_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:14:44.847125+00:00
-- url     : https://prove2.me/theorems/3f823bf0-77f2-4410-85da-2e85deace6bd
-- title:
--   Cert Grid G: n Parts poly T
-- statement:
--   The number of parts is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L126-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L126-L128

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

theorem ClauseBound.Alg.CertGridG.nParts_polyT {p d : α → ℕ} {tr : α → Bool} (hp : PolyT p) (hd : PolyT d) (ht : PolyT tr) :
    PolyT fun x => nParts (p x) (d x) (tr x) := by sorry
