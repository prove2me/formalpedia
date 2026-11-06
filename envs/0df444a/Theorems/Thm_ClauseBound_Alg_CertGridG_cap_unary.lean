-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_cap_unary
-- name    : ClauseBound.Alg.CertGridG.cap_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:28:39.755098+00:00
-- url     : https://prove2.me/theorems/7af52116-009e-4fa4-9836-b35d764ced72
-- title:
--   Cert Grid G: cap unary
-- statement:
--   The number of bits through which a piece factors is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L297-L299
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L297-L299

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
variable {P : PiecesF} (K : P.Keeps)
include K

theorem ClauseBound.Alg.CertGridG.cap_unary {tr : α → Bool} {h ℓ i : α → ℕ} (ht : PolyT tr) (hh : Unary h) (hℓ : Unary ℓ) (hi : PolyT i) :
    Unary fun x => P.cap (tr x) (h x) (ℓ x) (i x) := by sorry
