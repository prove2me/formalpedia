-- Prove2me | Theorems.Thm_Eight_sum_ofFn
-- name    : Eight.sum_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:08:45.037906+00:00
-- url     : https://prove2.me/theorems/d12e26d4-ef51-4033-8c75-358964f63ade
-- title:
--   Eight: sum of Fn
-- statement:
--   A sum over θ ∈ {0,1}^c, written as functions, is the sum over the words of c bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/App_Rate.lean#L28-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/App_Rate.lean#L28-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_Eight_App_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_App_Rate
set_option autoImplicit false
section
section
open Eight
open Finset Groundwork ClauseBound.Alg

theorem Eight.sum_ofFn (c : ℕ) (G : List Bool → ℤ) : ∑ θ : Pieces.Bits c, G (List.ofFn θ) = ∑ w ∈ words c, G w := by sorry
