-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Dummy_sum_fac
-- name    : ClauseBound.ParityChecks.Dummy.sum_fac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:16.419359+00:00
-- url     : https://prove2.me/theorems/7438730c-f02b-405f-85a7-b07c94bf3616
-- title:
--   Dummy: sum fac
-- statement:
--   The two values of the dummy variable of check j together.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L75-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L75-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Dummy
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype X] [Fintype E]

theorem ClauseBound.ParityChecks.Dummy.sum_fac (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (h : Disjoint J₁ J₂) (ξ : X) (j : Fin r) :
    ∑ b : Bool, fac V r Λ J₁ J₂ ξ j b =
      2 * ((if j ∈ J₁ then ev #(Λ j ∩ V ξ) else 1) * if j ∈ J₂ then (-1 : ℤ) ^ #(Λ j ∩ V ξ) else 1) := by sorry
