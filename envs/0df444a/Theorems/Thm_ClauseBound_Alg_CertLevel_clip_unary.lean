-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_clip_unary
-- name    : ClauseBound.Alg.CertLevel.clip_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:04:48.818046+00:00
-- url     : https://prove2.me/theorems/22d3fff5-d037-4957-956c-13e5062dc571
-- title:
--   Cert Level: clip unary
-- statement:
--   The number of nodes in a state that is cut off at a number in unary is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L493-L494
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L493-L494

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.clip_unary {M : α → ℕ} {st : α → NState} (hM : Unary M) (hst : PolyT st) : Unary fun x => (clip (M x) (st x)).2.2.1 := by sorry
