-- Prove2me | Theorems.Thm_ClauseBound_Alg_Need_le_of_size_le
-- name    : ClauseBound.Alg.Need.le_of_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:46.791619+00:00
-- url     : https://prove2.me/theorems/2cfe17e2-9374-4905-afd0-fb48b4148a9e
-- title:
--   Need: le of size le
-- statement:
--   A number with at most n binary digits is at most F if 2^n ≤ F.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Need.lean#L26-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Need.lean#L26-L27

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

theorem ClauseBound.Alg.Need.le_of_size_le {x n F : ℕ} (h : 2 ^ n ≤ F) (hx : Nat.size x ≤ n) : x ≤ F := by sorry
