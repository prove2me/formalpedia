-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertTop_entry_unary
-- name    : ClauseBound.Alg.CertTop.entry_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:31:07.634771+00:00
-- url     : https://prove2.me/theorems/67f2acf1-552b-4206-8882-51633802f914
-- title:
--   Cert Top: entry unary
-- statement:
--   The bound on the size of the entries of the top instance is given in unary if K and P are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L132-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L132-L134

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

theorem ClauseBound.Alg.CertTop.entry_unary {K P : α → ℕ} (hK : Unary K) (hP : Unary P) : Unary fun x => P x * (2 * (3 * K x ^ 8) / K x) := by sorry
