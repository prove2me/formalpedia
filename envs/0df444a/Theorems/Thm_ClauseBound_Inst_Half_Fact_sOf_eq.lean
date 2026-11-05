-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Fact_sOf_eq
-- name    : ClauseBound.Inst.Half.Fact.sOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:53:01.508204+00:00
-- url     : https://prove2.me/theorems/5bb8ffe4-95f9-407d-ba41-8e320b44ad6b
-- title:
--   Fact: s Of eq
-- statement:
--   s = i − 2h for the numbers of pieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfFact.lean#L33-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfFact.lean#L33-L34

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

theorem ClauseBound.Inst.Half.Fact.sOf_eq {h i : ℕ} (hi : i < 4 * h + 1) : sOf h i = (i : ℤ) - 2 * h := by sorry
