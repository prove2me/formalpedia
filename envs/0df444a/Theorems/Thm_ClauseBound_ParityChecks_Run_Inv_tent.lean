-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Run_Inv_tent
-- name    : ClauseBound.ParityChecks.Run.Inv.tent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:04.529514+00:00
-- url     : https://prove2.me/theorems/829e1ff5-7775-4893-a171-ec3ac03006e7
-- title:
--   Inv: tent
-- statement:
--   Both options of a decision satisfy the bounds for states that are tried.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L260-L264
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean#L260-L264

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

theorem ClauseBound.ParityChecks.Run.Inv.tent (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) {Ls : List Chk} {cur : Chk} {e : ℕ} (h : Inv q V ε Ls cur e) (he : e < q.m) :
    Tent q (lam q.m (Ls ++ [cur ++ [e]])) ∧ Tent q (lam q.m (Ls ++ [cur])) := by sorry
