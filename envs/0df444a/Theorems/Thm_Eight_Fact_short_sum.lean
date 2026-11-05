-- Prove2me | Theorems.Thm_Eight_Fact_short_sum
-- name    : Eight.Fact.short_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:54:30.874456+00:00
-- url     : https://prove2.me/theorems/d1121a43-443c-4632-a1e3-f7485d723c2c
-- title:
--   Fact: short sum
-- statement:
--   «Every function F : {0,1}^c × X' → ℤ factors through c bits, by F(z,z') = Σ_θ [z = θ]·F(θ,z')».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L246-L248
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L246-L248

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact

theorem Eight.Fact.short_sum {c : ℕ} {X : List Bool} (hX : X.length = c) (G : List Bool → ℤ) :
    ∑ θ ∈ words c, (if X = θ then 1 else 0) * G θ = G X := by sorry
