-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_size_n_le
-- name    : ClauseBound.TopN.Arith.size_n_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:50:13.003612+00:00
-- url     : https://prove2.me/theorems/f80079c8-ad46-4e46-8f82-981f992dda7c
-- title:
--   Arith: size n le
-- statement:
--   The number of binary digits of n is at most 17·C₀·Y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L145-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L145-L145

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_ClauseBound_TopN_Arith
set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
variable {k K n s C₀ : ℕ}

theorem ClauseBound.TopN.Arith.size_n_le (hlt : n < K ^ (17 * C₀)) : n.size ≤ 17 * C₀ * K.size := by sorry
