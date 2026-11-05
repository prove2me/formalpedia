-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_hF_polyT
-- name    : ClauseBound.Inst.Half.hF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:40:23.414622+00:00
-- url     : https://prove2.me/theorems/c58e684c-da40-4790-aa6e-2083c1b119d5
-- title:
--   Half: h F poly T
-- statement:
--   `hF c₀ lam` is polynomial-time in lam in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L79-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L79-L89

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

theorem ClauseBound.Inst.Half.hF_polyT (c₀ : ℕ) {lam : α → ℕ} (hl : Unary lam) : PolyT fun x => hF c₀ (lam x) := by sorry
