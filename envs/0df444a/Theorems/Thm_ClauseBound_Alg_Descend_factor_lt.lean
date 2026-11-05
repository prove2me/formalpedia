-- Prove2me | Theorems.Thm_ClauseBound_Alg_Descend_factor_lt
-- name    : ClauseBound.Alg.Descend.factor_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:35:22.774909+00:00
-- url     : https://prove2.me/theorems/1b518a4c-6d77-4774-a3a5-46c8ade6f27b
-- title:
--   Descend: factor lt
-- statement:
--   The factor after a step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L94-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L94-L98

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

theorem ClauseBound.Alg.Descend.factor_lt {f D z r x : ℕ} (hf : f < 2 ^ z) (hD : D ≤ 2 ^ r) : f * D < 2 ^ (z + r + x) := by sorry
