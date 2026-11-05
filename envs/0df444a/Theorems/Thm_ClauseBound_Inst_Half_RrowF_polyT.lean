-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_RrowF_polyT
-- name    : ClauseBound.Inst.Half.RrowF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:40:35.634522+00:00
-- url     : https://prove2.me/theorems/b2843b7d-f83c-4080-be56-ba205b6ae652
-- title:
--   Half: Rrow F poly T
-- statement:
--   The sum of the row-wise pieces is polynomial-time in h in unary and s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L96-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L96-L102

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

theorem ClauseBound.Inst.Half.RrowF_polyT {h : α → ℕ} {s : α → ℤ} (hh : Unary h) (hs : PolyT s) : PolyT fun x => RrowF (h x) (s x) := by sorry
