-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_len_pTab_le
-- name    : ClauseBound.Inst.Half.len_pTab_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:40:21.008733+00:00
-- url     : https://prove2.me/theorems/98d9644d-ba76-4ba1-8df3-4558a0ce2920
-- title:
--   Half: len p Tab le
-- statement:
--   The word of the table p(0), …, p(j) has length at most (j + 1) * (3 * (j + 1) + 4) + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L46-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L46-L55

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

theorem ClauseBound.Inst.Half.len_pTab_le (j : ℕ) : len (pTab j) ≤ (j + 1) * (3 * (j + 1) + 4) + 2 := by sorry
