-- Prove2me | Theorems.Thm_ExplicitCost_procedure_arith
-- name    : ExplicitCost.procedure_arith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:05:36.767+00:00
-- url     : https://prove2.me/theorems/37c50e80-252e-4a4e-82d1-dac8e876cf06
-- title:
--   Explicit Cost: procedure arith
-- statement:
--   The arithmetic: with A the price of a query one level up, G ≤ X^e, and a context of size at most
--   X^s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ProcedureCost.lean#L36-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ProcedureCost.lean#L36-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallFacts
import Definitions.Def_CountedRecursion_ParentSize
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ProcedureCost
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.procedure_arith {X A C₂ c₁ e s G sp : ℕ} (hX : 2 ≤ X) (hA : 2 ≤ A) (hG : G ≤ X ^ e) (hsp : sp ≤ X ^ s) :
    (A * X ^ C₂ + 2) * G ^ c₁ ≤ A * X ^ (C₂ + e * c₁ + s + 2) ∧ sp + G ^ c₁ + X ^ C₂ + 1 ≤ X ^ (C₂ + e * c₁ + s + 2) := by sorry
