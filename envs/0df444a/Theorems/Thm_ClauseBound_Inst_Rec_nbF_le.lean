-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_nbF_le
-- name    : ClauseBound.Inst.Rec.nbF_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:11:38.214204+00:00
-- url     : https://prove2.me/theorems/271274d4-b0ad-49eb-998f-0d413ce9de23
-- title:
--   Rec: nb F le
-- statement:
--   The Rec construction uses the nb F le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L127-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L127-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec

theorem ClauseBound.Inst.Rec.nbF_le (lam h b : ℕ) : nbF lam h b ≤ lam := by sorry
