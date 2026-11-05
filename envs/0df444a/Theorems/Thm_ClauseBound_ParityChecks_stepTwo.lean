-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_stepTwo
-- name    : ClauseBound.ParityChecks.stepTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:00:12.946886+00:00
-- url     : https://prove2.me/theorems/54c421d6-4081-4514-af1d-791c8060eafc
-- title:
--   Parity Checks: step Two
-- statement:
--   The choice of the checks by conditional expectations (`ParityChecks.ChoiceByPotential`): a
--   variant of Step 2 of Appendix D that chooses the checks by a potential of four terms instead of by
--   Lemma 13. Here are its mathematical statements, without the program that carries it out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ChoiceByPotential.lean#L28-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ChoiceByPotential.lean#L28-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Martingale
import Definitions.Def_ClauseBound_ParityChecks_Start
import Definitions.Def_ClauseBound_ParityChecks_Structure
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_ChoiceByPotential
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.stepTwo : _root_.ParityChecks.ChoiceByPotential := by sorry
