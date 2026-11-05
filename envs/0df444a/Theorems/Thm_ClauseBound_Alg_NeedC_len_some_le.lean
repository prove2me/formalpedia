-- Prove2me | Theorems.Thm_ClauseBound_Alg_NeedC_len_some_le
-- name    : ClauseBound.Alg.NeedC.len_some_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:35:27.799844+00:00
-- url     : https://prove2.me/theorems/978f4f26-6acd-45a5-87c7-131bef656b89
-- title:
--   Need C: len some le
-- statement:
--   The word of a state is short.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L58-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L58-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F

theorem ClauseBound.Alg.NeedC.len_some_le (P : PiecesF) (st : NState) (sched : List Step) {b : ℕ} (h : tot P st sched ≤ b) : len (some st) ≤ 100 * (b + 2) := by sorry
