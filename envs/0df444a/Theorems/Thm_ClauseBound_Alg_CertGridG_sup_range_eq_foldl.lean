-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_sup_range_eq_foldl
-- name    : ClauseBound.Alg.CertGridG.sup_range_eq_foldl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:59:59.574236+00:00
-- url     : https://prove2.me/theorems/cae118da-2713-4f47-af85-3966d96558d1
-- title:
--   Cert Grid G: sup range eq foldl
-- statement:
--   The largest of f 0, …, f (n − 1) as a fold.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L212-L217
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L212-L217

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

theorem ClauseBound.Alg.CertGridG.sup_range_eq_foldl (n : ℕ) (f : ℕ → ℕ) : (Finset.range n).sup f = (List.range n).foldl (fun c i => max c (f i)) 0 := by sorry
