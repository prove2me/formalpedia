-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_hasV_append_singleton
-- name    : ClauseBound.ParityChecks.Shape.hasV_append_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:48:32.347089+00:00
-- url     : https://prove2.me/theorems/4ceaa76f-8e59-4ea6-8cb5-ad628110aeae
-- title:
--   Shape: has V append singleton
-- statement:
--   A literal more.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L90-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L90-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.Shape.hasV_append_singleton (v : ℕ) (C : List (ℕ × Bool)) (l : ℕ × Bool) : hasV v (C ++ [l]) = (hasV v C || l.1 == v) := by sorry
