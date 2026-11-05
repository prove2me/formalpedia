-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_Inv_step
-- name    : ClauseBound.ParityChecks.Run.Inv.step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:38.536494+00:00
-- url     : https://prove2.me/theorems/16718a2d-905f-4d6b-a193-f1be4de120e4
-- title:
--   Inv: step
-- statement:
--   One decision keeps the invariant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L267-L312
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L267-L312

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

theorem ClauseBound.ParityChecks.Run.Inv.step (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) {Ls : List Chk} {cur : Chk} {e : ℕ} (h : Inv q V ε Ls cur e)
    (he : e < q.m) : Inv q V ε Ls (q.decide1 orcA orcB Ls cur e) (e + 1) := by sorry
