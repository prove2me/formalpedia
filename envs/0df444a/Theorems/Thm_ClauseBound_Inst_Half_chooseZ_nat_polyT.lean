-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_chooseZ_nat_polyT
-- name    : ClauseBound.Inst.Half.chooseZ_nat_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:49.021519+00:00
-- url     : https://prove2.me/theorems/093e41ec-c731-44a6-a703-ba67df7f6c6d
-- title:
--   Half: choose Z nat poly T
-- statement:
--   A binomial coefficient with a natural number in unary on top; the lower number may be in binary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L134-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L134-L137

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

theorem ClauseBound.Inst.Half.chooseZ_nat_polyT {a i : α → ℕ} (ha : Unary a) (hi : PolyT i) : PolyT fun x => chooseZ (a x : ℤ) (i x) := by sorry
