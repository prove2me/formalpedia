-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_RunF_lenChk_le_big
-- name    : ClauseBound.ParityChecks.RunF.lenChk_le_big
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:22.717114+00:00
-- url     : https://prove2.me/theorems/6aae1b39-e9be-4e9c-a76b-9d3523473622
-- title:
--   Run F: len Chk le big
-- statement:
--   The word of a check is shorter than the length that the program asks of the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L116-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L116-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}

theorem ClauseBound.ParityChecks.RunF.lenChk_le_big {n Δ : ℕ} (hm : q.m ≤ Δ * n) : lenChk q.m ≤ 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) + 8 := by sorry
