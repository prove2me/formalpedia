-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_sum_split
-- name    : ClauseBound.ParityChecks.Num.sum_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:28.973945+00:00
-- url     : https://prove2.me/theorems/dd53aafe-1150-4012-8a8b-9d9ed0f297ef
-- title:
--   Num: sum split
-- statement:
--   A sum over 0, …, r − 1, split at j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L54-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L54-L58

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

theorem ClauseBound.ParityChecks.Num.sum_split {M : Type} [AddCommMonoid M] (f : ℕ → M) {j r : ℕ} (hj : j < r) :
    ∑ i ∈ range r, f i = ∑ i ∈ range j, f i + f j + ∑ i ∈ range (r - 1 - j), f (j + 1 + i) := by sorry
