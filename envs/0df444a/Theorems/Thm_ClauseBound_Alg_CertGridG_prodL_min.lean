-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_prodL_min
-- name    : ClauseBound.Alg.CertGridG.prodL_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:59:06.135318+00:00
-- url     : https://prove2.me/theorems/0e2036ac-62e3-4bf5-afed-d3f0d38ad122
-- title:
--   Cert Grid G: prod L min
-- statement:
--   A product over j < n only needs its factors for j ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L88-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L88-L90

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

theorem ClauseBound.Alg.CertGridG.prodL_min (n : ℕ) (f : ℕ → ℤ) : prodL n (fun j => f (min j n)) = prodL n f := by sorry
