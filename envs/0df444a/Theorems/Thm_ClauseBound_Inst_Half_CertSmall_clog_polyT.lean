-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_CertSmall_clog_polyT
-- name    : ClauseBound.Inst.Half.CertSmall.clog_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:12.627341+00:00
-- url     : https://prove2.me/theorems/c6b8f728-4b36-40af-911d-dc52edef454d
-- title:
--   Cert Small: clog poly T
-- statement:
--   The least k with n ≤ 2^k is polynomial-time in n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean#L32-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean#L32-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.CertSmall
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.CertSmall.clog_polyT {n : α → ℕ} (hn : PolyT n) : PolyT fun x => Nat.clog 2 (n x) := by sorry
