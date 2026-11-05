-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Ev_length_rep
-- name    : ClauseBound.ParityChecks.Ev.length_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:09.540071+00:00
-- url     : https://prove2.me/theorems/3a535ef4-6dc0-4cc4-8df4-fab145d30b3d
-- title:
--   Ev: length rep
-- statement:
--   The length of n in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L28-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L28-L28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Ev
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Ev
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW

theorem ClauseBound.ParityChecks.Ev.length_rep (n : ℕ) : (rep n).length = n := by sorry
