-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertTop_PtopK_unary
-- name    : ClauseBound.Alg.CertTop.PtopK_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:44:42.320173+00:00
-- url     : https://prove2.me/theorems/3cae2d20-d43c-421f-ac92-aefba8fbfe40
-- title:
--   Cert Top: Ptop K unary
-- statement:
--   The bound P of the network of a k-CNF is given in unary if g, k and m are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L121-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L121-L123

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

theorem ClauseBound.Alg.CertTop.PtopK_unary {g k m : α → ℕ} (hg : Unary g) (hk : Unary k) (hm : Unary m) : Unary fun x => PtopK (g x) (k x) (m x) := by sorry
