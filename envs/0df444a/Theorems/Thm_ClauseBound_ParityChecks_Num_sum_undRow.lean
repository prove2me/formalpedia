-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_sum_undRow
-- name    : ClauseBound.ParityChecks.Num.sum_undRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:03.024551+00:00
-- url     : https://prove2.me/theorems/4ebb027d-576d-4751-aee4-52334f68c46b
-- title:
--   Num: sum und Row
-- statement:
--   The number of undecided pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L181-L183
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L181-L183

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
variable {q}

theorem ClauseBound.ParityChecks.Num.sum_undRow (m e : ℕ) {j r : ℕ} (hj : j < r) : ∑ j' ∈ range r, undRow j (Dset m e) j' = (m - e) + (r - 1 - j) * m := by sorry
