-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_K_succ
-- name    : ClauseBound.Gen.Pick.K_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:47:31.649997+00:00
-- url     : https://prove2.me/theorems/192dbeb7-d9d7-49bb-9621-79d514897754
-- title:
--   Pick: K succ
-- statement:
--   The Pick construction uses the K succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L31-L31

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

theorem ClauseBound.Gen.Pick.K_succ (x₀ l : ℕ) : K x₀ (l + 1) = g x₀ l ^ 2 := by sorry
