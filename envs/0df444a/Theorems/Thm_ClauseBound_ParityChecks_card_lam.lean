-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_card_lam
-- name    : ClauseBound.ParityChecks.card_lam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:23.075823+00:00
-- url     : https://prove2.me/theorems/504a75ac-46ec-4cc3-a715-15792a2f76ca
-- title:
--   Parity Checks: card lam
-- statement:
--   A check as a set has as many elements as its list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L118-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L118-L123

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))

theorem ClauseBound.ParityChecks.card_lam {Ls : List Chk} (hL : ∀ L ∈ Ls, ChkOK q.m L) (j : ℕ) : #(lam q.m Ls j) = (Ls.getD j []).length := by sorry
