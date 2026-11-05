-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_nodeG_polyT
-- name    : ClauseBound.Alg.CertGridG.nodeG_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:14:18.045098+00:00
-- url     : https://prove2.me/theorems/9b1f3c3b-c32d-4704-a712-06c095137fd7
-- title:
--   Cert Grid G: node G poly T
-- statement:
--   The position of a node of a part is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L136-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L136-L138

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

theorem ClauseBound.Alg.CertGridG.nodeG_polyT {d a i : α → ℕ} {tr : α → Bool} (hd : PolyT d) (ht : PolyT tr) (ha : PolyT a) (hi : PolyT i) :
    PolyT fun x => nodeG (d x) (tr x) (a x) (i x) := by sorry
