-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_count_unary
-- name    : ClauseBound.Inst.Half.count_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:11:11.838569+00:00
-- url     : https://prove2.me/theorems/020d3513-12b4-4ab4-83d2-cb58e3d6e293
-- title:
--   Half: count unary
-- statement:
--   The number of occurrences in a list is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L36-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L36-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Theorems.Thm_Groundwork_PolyT_count
attribute [local fun_prop] Groundwork.PolyT.count


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Inst.Rec
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.count_unary {l : α → List ℕ} {a : α → ℕ} (hl : PolyT l) (ha : PolyT a) : Unary fun x => (l x).count (a x) := by sorry
