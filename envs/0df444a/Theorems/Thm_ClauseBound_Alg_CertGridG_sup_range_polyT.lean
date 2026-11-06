-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_sup_range_polyT
-- name    : ClauseBound.Alg.CertGridG.sup_range_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:59:34.317207+00:00
-- url     : https://prove2.me/theorems/d9f1f4e2-4270-4363-96e5-8c23fa9b0448
-- title:
--   Cert Grid G: sup range poly T
-- statement:
--   The largest of f 0, …, f (n − 1) is polynomial-time, for n in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L220-L230
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L220-L230

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

theorem ClauseBound.Alg.CertGridG.sup_range_polyT {n : α → ℕ} {f : α → ℕ → ℕ} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 p.2) :
    PolyT fun x => (Finset.range (n x)).sup (f x) := by sorry
