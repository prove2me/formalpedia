-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertTop_unary_max
-- name    : ClauseBound.Alg.CertTop.unary_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:43:03.379003+00:00
-- url     : https://prove2.me/theorems/69e92f1b-e125-4c94-a7ef-24a3f8ac6377
-- title:
--   Cert Top: unary max
-- statement:
--   The larger of two numbers given in unary is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L108-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L108-L109

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

theorem ClauseBound.Alg.CertTop.unary_max {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun x => max (f x) (g x) := by sorry
