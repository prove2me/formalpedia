-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_erase_polyT
-- name    : ClauseBound.Inst.Half.erase_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:00:21.346192+00:00
-- url     : https://prove2.me/theorems/b9516b0e-9e0f-4fca-b354-f65b204228cd
-- title:
--   Half: erase poly T
-- statement:
--   Erasing the first occurrence of a number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L31-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L31-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfTab
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Inst.Rec
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.erase_polyT {l : α → List ℕ} {a : α → ℕ} (hl : PolyT l) (ha : PolyT a) : PolyT fun x => (l x).erase (a x) := by sorry
