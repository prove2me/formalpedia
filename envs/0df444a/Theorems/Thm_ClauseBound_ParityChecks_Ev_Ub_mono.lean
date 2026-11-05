-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Ev_Ub_mono
-- name    : ClauseBound.ParityChecks.Ev.Ub_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:36.818076+00:00
-- url     : https://prove2.me/theorems/e4a08e6b-fda2-4586-87db-44635167787a
-- title:
--   Ev: Ub mono
-- statement:
--   The bound for the total of the network of marks grows with the number of variables, the cap and
--   the number of layers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L32-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Ev.lean#L32-L36

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

theorem ClauseBound.ParityChecks.Ev.Ub_mono (k g β : ℕ) {n n' w w' R R' : ℕ} (hn : n ≤ n') (hw : w ≤ w') (h : R ≤ R') : Ub k g n w β R ≤ Ub k g n' w' β R' := by sorry
