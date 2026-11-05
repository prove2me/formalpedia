-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_hF_unary
-- name    : ClauseBound.Inst.Half.hF_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:21:09.607535+00:00
-- url     : https://prove2.me/theorems/dc808d13-3ec3-4f71-8a1b-c16b7f24d6d0
-- title:
--   Half: h F unary
-- statement:
--   `hF c₀ lam` is given in unary if lam is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L92-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L92-L93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfPart
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.hF_unary (c₀ : ℕ) {lam : α → ℕ} (hl : Unary lam) : Unary fun x => hF c₀ (lam x) := by sorry
