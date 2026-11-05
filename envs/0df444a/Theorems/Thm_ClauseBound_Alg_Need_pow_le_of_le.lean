-- Prove2me | Theorems.Thm_ClauseBound_Alg_Need_pow_le_of_le
-- name    : ClauseBound.Alg.Need.pow_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:04.41239+00:00
-- url     : https://prove2.me/theorems/a3f5ddd7-75c9-48e5-8470-a642eee31dbb
-- title:
--   Need: pow le of le
-- statement:
--   2^a ≤ F if a ≤ n and 2^n ≤ F.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Need.lean#L30-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Need.lean#L30-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_Need
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Need
open PaddedDescent.F

theorem ClauseBound.Alg.Need.pow_le_of_le {a n F : ℕ} (h : 2 ^ n ≤ F) (ha : a ≤ n) : 2 ^ a ≤ F := by sorry
