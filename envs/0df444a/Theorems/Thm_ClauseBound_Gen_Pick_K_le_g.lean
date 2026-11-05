-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_K_le_g
-- name    : ClauseBound.Gen.Pick.K_le_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:18:54.0752+00:00
-- url     : https://prove2.me/theorems/e26ff0d7-a5b1-40e3-bf72-26145c6fe1b6
-- title:
--   Pick: K le g
-- statement:
--   The Pick construction uses the K le g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L36-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L36-L36

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

theorem ClauseBound.Gen.Pick.K_le_g (x₀ l : ℕ) : K x₀ l ≤ g x₀ l := by sorry
