-- Prove2me | Theorems.Thm_ClauseBound_Alg_Need_pow_le_two_pow_size
-- name    : ClauseBound.Alg.Need.pow_le_two_pow_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:06.717406+00:00
-- url     : https://prove2.me/theorems/9b740349-15a8-4b7c-acef-ff3063e94b2c
-- title:
--   Need: pow le two pow size
-- statement:
--   K^p ≤ 2^(p · number of binary digits of K).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Need.lean#L34-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Need.lean#L34-L36

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

theorem ClauseBound.Alg.Need.pow_le_two_pow_size (K p : ℕ) : K ^ p ≤ 2 ^ (p * Nat.size K) := by sorry
