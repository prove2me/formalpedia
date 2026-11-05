-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_RunF_lenChk_add_two_le
-- name    : ClauseBound.ParityChecks.RunF.lenChk_add_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:48:10.469377+00:00
-- url     : https://prove2.me/theorems/d7727ffa-8e4e-4e05-98df-8b2316a194b5
-- title:
--   Run F: len Chk add two le
-- statement:
--   The bound for one check, in terms of bounds for m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L105-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L105-L109

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

theorem ClauseBound.ParityChecks.RunF.lenChk_add_two_le {n Δ : ℕ} (hm : q.m ≤ Δ * n) : lenChk q.m + 2 ≤ 8 * ((Δ * n + 1) * (Nat.size (Δ * n) + 2)) := by sorry
