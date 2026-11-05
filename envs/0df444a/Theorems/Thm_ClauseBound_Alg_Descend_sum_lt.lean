-- Prove2me | Theorems.Thm_ClauseBound_Alg_Descend_sum_lt
-- name    : ClauseBound.Alg.Descend.sum_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:29.195015+00:00
-- url     : https://prove2.me/theorems/fc9231b6-0d52-4dc8-9a7c-16cf6c23eadc
-- title:
--   Descend: sum lt
-- statement:
--   The sum after a step: the old sum a times D, plus b, the sum of at most cnt terms below
--   2^(digits of n + E).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L102-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L102-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Descend
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists

theorem ClauseBound.Alg.Descend.sum_lt {a b : ℤ} {D z r cnt n E : ℕ} (ha : a.natAbs < 2 ^ z) (hD : D ≤ 2 ^ r) (hn : 1 ≤ n)
    (hb : b.natAbs ≤ cnt * 2 ^ (Nat.size n + E)) : (a * (D : ℕ) + b).natAbs < 2 ^ (z + r + Nat.size (cnt * n) + E + 2) := by sorry
