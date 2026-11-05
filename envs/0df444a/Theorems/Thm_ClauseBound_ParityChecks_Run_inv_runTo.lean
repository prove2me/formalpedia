-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_inv_runTo
-- name    : ClauseBound.ParityChecks.Run.inv_runTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:55.167189+00:00
-- url     : https://prove2.me/theorems/840e33f1-54aa-4478-9787-19473e2cd147
-- title:
--   Run: inv run To
-- statement:
--   The decisions for one check keep the invariant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L328-L336
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L328-L336

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

theorem ClauseBound.ParityChecks.Run.inv_runTo (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) {Ls : List Chk} (h : Inv q V ε Ls [] 0) :
    ∀ e ≤ q.m, Inv q V ε Ls (q.runTo orcA orcB Ls e) e := by sorry
