-- Prove2me | Theorems.Thm_ClauseBound_Gen_Seq_two_le_K
-- name    : ClauseBound.Gen.Seq.two_le_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:15:59.151477+00:00
-- url     : https://prove2.me/theorems/cc72527a-7339-49d9-87bd-29090bbdc90f
-- title:
--   Seq: two le K
-- statement:
--   K_l ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Seq.lean#L35-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Seq.lean#L35-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Seq
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
open ClauseBound.Gen.Seq

theorem ClauseBound.Gen.Seq.two_le_K (x₀ l : ℕ) (hx : 18 ≤ x₀) : 2 ≤ K x₀ l := by sorry
