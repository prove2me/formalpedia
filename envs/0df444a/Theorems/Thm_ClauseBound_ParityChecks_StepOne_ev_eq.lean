-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_ev_eq
-- name    : ClauseBound.ParityChecks.StepOne.ev_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:24.248772+00:00
-- url     : https://prove2.me/theorems/e73e5cb0-780b-49cd-bd43-5daaf8f091a7
-- title:
--   Step One: ev eq
-- statement:
--   [q even] = Σ_i σ_i·C(q,i).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L61-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L61-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks

theorem ClauseBound.ParityChecks.StepOne.ev_eq (q : ℕ) : ev q = ∑ i ∈ range (q + 1), sig i * q.choose i := by sorry
