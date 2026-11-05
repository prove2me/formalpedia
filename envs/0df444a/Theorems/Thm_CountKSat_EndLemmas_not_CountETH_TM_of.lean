-- Prove2me | Theorems.Thm_CountKSat_EndLemmas_not_CountETH_TM_of
-- name    : CountKSat.EndLemmas.not_CountETH_TM_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:15.036473+00:00
-- url     : https://prove2.me/theorems/eff495c9-c781-4f80-ac1a-2844964c58d0
-- title:
--   End Lemmas: not Count ETH TM of
-- statement:
--   The hypothesis fails if #3-SAT is in time O(2^{δn}) for every δ > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/EndLemmas.lean#L30-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/EndLemmas.lean#L30-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Definitions.Def_CountKSat_EndLemmas
set_option autoImplicit false
section
open CountKSat CountKSat.EndLemmas
open Turing SatK
open scoped NNReal ENNReal

theorem CountKSat.EndLemmas.not_CountETH_TM_of (h : ∀ δ : ℝ≥0, 0 < δ → CountInTimeTM 3 δ) : ¬ CountETH_TM := by sorry
