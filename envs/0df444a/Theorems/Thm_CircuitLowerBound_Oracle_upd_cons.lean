-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_upd_cons
-- name    : CircuitLowerBound.Oracle.upd_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:36.772651+00:00
-- url     : https://prove2.me/theorems/ac28eec0-a492-4c86-ac15-fb8e9dc988ae
-- title:
--   Oracle: upd cons
-- statement:
--   The Oracle construction uses the upd cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L30-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L30-L36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Runs
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable {M : TM2ComputableAux Bool Bool} (O : Lang)

theorem CircuitLowerBound.Oracle.upd_cons {s d : NS} (hsd : s ≠ d) (n : NS → List Bool) (b : Bool) (l : List Bool) :
    Function.update (Function.update (Function.update (Function.update n s l) d (b :: n d)) s []) d (l.reverse ++ b :: n d)
      = Function.update (Function.update n s []) d ((b :: l).reverse ++ n d) := by sorry
