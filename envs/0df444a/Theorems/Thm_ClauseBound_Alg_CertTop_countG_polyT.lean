-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertTop_countG_polyT
-- name    : ClauseBound.Alg.CertTop.countG_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:00.265412+00:00
-- url     : https://prove2.me/theorems/7bd8b28e-54f1-44be-9c08-b886d10aeb00
-- title:
--   Cert Top: count G poly T
-- statement:
--   The value of the network of a formula is polynomial-time jointly in the pad, the index, k in
--   unary and the formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L151-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L151-L160

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
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

theorem ClauseBound.Alg.CertTop.countG_polyT (hS : StCertSatK) (hR : StCertRebalG) (hP : S.Poly) {pad : α → U} {i : α → Idx} {ku : α → U} {ψ : α → Fml}
    (hp : PolyT pad) (hi : PolyT i) (hk : PolyT ku) (hψ : PolyT ψ) : PolyT fun x => countG S (pad x) (i x) (ku x) (ψ x) := by sorry
