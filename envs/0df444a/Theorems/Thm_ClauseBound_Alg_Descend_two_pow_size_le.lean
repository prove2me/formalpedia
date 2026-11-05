-- Prove2me | Theorems.Thm_ClauseBound_Alg_Descend_two_pow_size_le
-- name    : ClauseBound.Alg.Descend.two_pow_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:46.216236+00:00
-- url     : https://prove2.me/theorems/3993453b-b104-4fe3-91fe-fc062ab15604
-- title:
--   Descend: two pow size le
-- statement:
--   2^(number of binary digits of n) ≤ 2n for n ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L87-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L87-L91

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

theorem ClauseBound.Alg.Descend.two_pow_size_le {n : ℕ} (h : 1 ≤ n) : 2 ^ Nat.size n ≤ 2 * n := by sorry
