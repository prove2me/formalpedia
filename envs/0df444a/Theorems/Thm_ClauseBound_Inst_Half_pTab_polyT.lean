-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_pTab_polyT
-- name    : ClauseBound.Inst.Half.pTab_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:26:20.214785+00:00
-- url     : https://prove2.me/theorems/fe041873-8fd1-4f9b-9835-6d2d9d87e20e
-- title:
--   Half: p Tab poly T
-- statement:
--   The table p(0), …, p(W) is polynomial-time in W in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L58-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L58-L72

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

theorem ClauseBound.Inst.Half.pTab_polyT {W : α → ℕ} (hW : Unary W) : PolyT fun x => pTab (W x) := by sorry
