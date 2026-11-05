-- Prove2me | Theorems.Thm_ClauseBound_Gen_Seq_topK_idx
-- name    : ClauseBound.Gen.Seq.topK_idx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:01:45.180201+00:00
-- url     : https://prove2.me/theorems/0cad2949-57ba-4c53-a658-3ccf417cbc9a
-- title:
--   Seq: top K idx
-- statement:
--   The solver has K_l nodes at the index of level l.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Seq.lean#L29-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Seq.lean#L29-L32

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

theorem ClauseBound.Gen.Seq.topK_idx (P : PiecesF) (x₀ l : ℕ) : topK (idx P x₀ l) = K x₀ l := by sorry
