-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Ev_Pb_mono
-- name    : ClauseBound.ParityChecks.Ev.Pb_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:09.608016+00:00
-- url     : https://prove2.me/theorems/3e3346a7-dffe-4ddb-a951-7d701fe71737
-- title:
--   Ev: Pb mono
-- statement:
--   The bound for the size of the network of marks grows with the number of variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L39-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L39-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Ev
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Ev
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW

theorem ClauseBound.ParityChecks.Ev.Pb_mono (g β D : ℕ) {n n' : ℕ} (hn : n ≤ n') : Pb g n β D ≤ Pb g n' β D := by sorry
