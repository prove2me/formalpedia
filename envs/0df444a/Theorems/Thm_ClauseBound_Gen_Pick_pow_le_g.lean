-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_pow_le_g
-- name    : ClauseBound.Gen.Pick.pow_le_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:25:18.024833+00:00
-- url     : https://prove2.me/theorems/de926d9b-41cd-4924-9d7e-704ff5613d9f
-- title:
--   Pick: pow le g
-- statement:
--   The Pick construction uses the pow le g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L38-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L38-L38

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

theorem ClauseBound.Gen.Pick.pow_le_g (x₀ l : ℕ) : 2 ^ (3 * l + x₀) ≤ g x₀ l := by sorry
