-- Prove2me | Theorems.Thm_CountKSat_stProgC
-- name    : CountKSat.stProgC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:07:07.34318+00:00
-- url     : https://prove2.me/theorems/de7e2c7c-3ef6-4022-97fc-bb9cbe1b0ded
-- title:
--   Count KSat: st Prog C
-- statement:
--   The sparsification lemma for counting, for the thresholds `theta τ`, from the three interface
--   statements on counts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L202-L230
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L202-L230

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_ProgC
set_option autoImplicit false
section
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog

theorem CountKSat.stProgC (hSC : StStepCount) (hRC : StRootCount) (hSL : StSumLeaves) : StProgC := by sorry
