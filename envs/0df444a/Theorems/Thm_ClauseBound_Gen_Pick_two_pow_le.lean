-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_two_pow_le
-- name    : ClauseBound.Gen.Pick.two_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:11:58.676248+00:00
-- url     : https://prove2.me/theorems/bcac0b6c-5191-4a10-a7f2-28dc3d345182
-- title:
--   Pick: two pow le
-- statement:
--   The Pick construction uses the two pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L42-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L42-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

theorem ClauseBound.Gen.Pick.two_pow_le (x₀ l : ℕ) : 2 ^ l ≤ 2 ^ (3 * l + x₀) := by sorry
