-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_chunkAt_polyT
-- name    : ClauseBound.Alg.CertGridG.chunkAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:59:35.364664+00:00
-- url     : https://prove2.me/theorems/4c6cc056-8a99-4ca0-87b8-e151046e4e31
-- title:
--   Cert Grid G: chunk At poly T
-- statement:
--   A chunk of a word, for lengths that are polynomial-time and a chunk number given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L98-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L98-L103

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

theorem ClauseBound.Alg.CertGridG.chunkAt_polyT {n : α → ℕ → ℕ} {κ : α → ℕ} {w : α → List Bool} (hn : PolyT fun p : α × ℕ => n p.1 p.2) (hκ : Unary κ) (hw : PolyT w) :
    PolyT fun x => chunkAt (n x) (κ x) (w x) := by sorry
