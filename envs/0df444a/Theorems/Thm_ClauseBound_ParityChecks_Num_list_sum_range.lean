-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_list_sum_range
-- name    : ClauseBound.ParityChecks.Num.list_sum_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:14.756203+00:00
-- url     : https://prove2.me/theorems/a3894dfb-1b1f-4b08-8827-369cf5819940
-- title:
--   Num: list sum range
-- statement:
--   The sum of a list of values at 0, …, n − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L39-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L39-L42

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
open ClauseBound.ParityChecks.Num

theorem ClauseBound.ParityChecks.Num.list_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by sorry
