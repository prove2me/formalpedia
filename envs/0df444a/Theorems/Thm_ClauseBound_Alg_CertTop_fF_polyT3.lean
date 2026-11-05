-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertTop_fF_polyT3
-- name    : ClauseBound.Alg.CertTop.fF_polyT3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:43:06.464206+00:00
-- url     : https://prove2.me/theorems/fdf96f03-0062-432f-9011-d0fb805336ad
-- title:
--   Cert Top: f F poly T3
-- statement:
--   The factor of two groups of clauses at a state word and a label word, jointly in g, k in unary,
--   the formula and the query.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L79-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L79-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_CertCount
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ClauseBound_Alg_CertTop
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg.CertCount CountKSat CountKSat.Poly
variable {α : Type} [Enc α]

theorem ClauseBound.Alg.CertTop.fF_polyT3 {g k : α → ℕ} {q : α → Fml × FQ} (hg : PolyT g) (hk : Unary k) (hq : PolyT q) :
    PolyT fun x => fF (g x) (k x) (q x) := by sorry
