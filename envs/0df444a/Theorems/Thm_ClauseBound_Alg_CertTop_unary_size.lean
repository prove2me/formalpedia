-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertTop_unary_size
-- name    : ClauseBound.Alg.CertTop.unary_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:43:32.183546+00:00
-- url     : https://prove2.me/theorems/c1ede21b-c800-4741-9d13-9c5872a9f45c
-- title:
--   Cert Top: unary size
-- statement:
--   The number of binary digits of a number given in unary is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L112-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L112-L113

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

theorem ClauseBound.Alg.CertTop.unary_size {f : α → ℕ} (hf : Unary f) : Unary fun x => Nat.size (f x) := by sorry
