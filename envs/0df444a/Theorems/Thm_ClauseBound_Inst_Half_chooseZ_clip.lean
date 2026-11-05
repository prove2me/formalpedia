-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_chooseZ_clip
-- name    : ClauseBound.Inst.Half.chooseZ_clip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:14.639613+00:00
-- url     : https://prove2.me/theorems/4901da51-91f6-4c18-9a71-53ac5e9bb290
-- title:
--   Half: choose Z clip
-- statement:
--   A binomial coefficient with a natural number on top vanishes when the lower number is larger.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L128-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L128-L131

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

theorem ClauseBound.Inst.Half.chooseZ_clip (a i : ℕ) : chooseZ (a : ℤ) i = if i ≤ a then chooseZ (a : ℤ) (min i a) else 0 := by sorry
