-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_loop_polyT
-- name    : ClauseBound.Gen.Pick.loop_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:47:40.977277+00:00
-- url     : https://prove2.me/theorems/8b185d6e-4354-4d52-85d8-cdb7c2c75f0d
-- title:
--   Pick: loop poly T
-- statement:
--   The Pick construction uses the loop poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L171-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L171-L175

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

theorem ClauseBound.Gen.Pick.loop_polyT (P : PiecesF) (x₀ : ℕ) : PolyT (loop P x₀) := by sorry
