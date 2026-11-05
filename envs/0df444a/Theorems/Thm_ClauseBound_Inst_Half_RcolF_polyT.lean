-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_RcolF_polyT
-- name    : ClauseBound.Inst.Half.RcolF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:40:29.195885+00:00
-- url     : https://prove2.me/theorems/b4fe63a2-7006-4df6-ab1d-fde4a8fc6797
-- title:
--   Half: Rcol F poly T
-- statement:
--   The sum of the column-wise pieces is polynomial-time in h in unary and s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L105-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L105-L113

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

theorem ClauseBound.Inst.Half.RcolF_polyT {h : α → ℕ} {s : α → ℤ} (hh : Unary h) (hs : PolyT s) : PolyT fun x => RcolF (h x) (s x) := by sorry
