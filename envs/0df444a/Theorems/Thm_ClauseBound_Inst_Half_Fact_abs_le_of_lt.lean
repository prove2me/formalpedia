-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Fact_abs_le_of_lt
-- name    : ClauseBound.Inst.Half.Fact.abs_le_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:53:13.436383+00:00
-- url     : https://prove2.me/theorems/5de5d87e-40eb-47a8-9139-939631742336
-- title:
--   Fact: abs le of lt
-- statement:
--   The Fact construction uses the abs le of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfFact.lean#L36-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfFact.lean#L36-L36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfFact
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Finset
open ClauseBound.Inst.Half.Fact

theorem ClauseBound.Inst.Half.Fact.abs_le_of_lt {h i : ℕ} (hi : i < 4 * h + 1) : |(i : ℤ) - 2 * h| ≤ 2 * (h : ℤ) := by sorry
