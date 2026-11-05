-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_inv_runChecks
-- name    : ClauseBound.ParityChecks.Run.inv_runChecks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:09.076197+00:00
-- url     : https://prove2.me/theorems/87e6df54-4c08-40cf-9713-4e2b39ff18f9
-- title:
--   Run: inv run Checks
-- statement:
--   At the beginning of every check the invariant holds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L339-L382
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L339-L382

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
variable {V} {orcA orcB} {ε : ℚ}

theorem ClauseBound.ParityChecks.Run.inv_runChecks (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) :
    ∀ j < q.r, (q.runChecks orcA orcB j).length = j ∧ Inv q V ε (q.runChecks orcA orcB j) [] 0 := by sorry
