-- Prove2me | Theorems.Thm_ClauseBound_Alg_Level_parts_eq
-- name    : ClauseBound.Alg.Level.parts_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:41.478182+00:00
-- url     : https://prove2.me/theorems/f3c16c69-422e-4e7c-8005-9efa7602d7d1
-- title:
--   Level: parts eq
-- statement:
--   The network that is rebalanced has p nodes, each of them d merged nodes of the grid: it is the
--   row network, or the grid is square.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Level.lean#L111-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Level.lean#L111-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_Good
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Level
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset

theorem ClauseBound.Alg.Level.parts_eq (s : Step) (hsq : s.thin = false → s.p = s.d) (c : Bool) :
    nParts s.p s.d (!s.thin && c) = s.p ∧ nMemb s.p s.d (!s.thin && c) = s.d := by sorry
