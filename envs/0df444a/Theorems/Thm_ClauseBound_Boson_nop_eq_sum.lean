-- Prove2me | Theorems.Thm_ClauseBound_Boson_nop_eq_sum
-- name    : ClauseBound.Boson.nop_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:58.75456+00:00
-- url     : https://prove2.me/theorems/175218bc-ec3b-4d1b-b6d3-6ddce98b2d1a
-- title:
--   Boson: nop eq sum
-- statement:
--   In `nop` the two index sets may be replaced by any larger finite sets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L106-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L106-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Basic
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open Basic

theorem ClauseBound.Boson.nop_eq_sum (n : ℕ) (F : ℤ → Ker) (r : ℤ) (π σ : Multiset ℕ) {S T : Finset ℕ} (hS : π.toFinset ⊆ S) (hT : σ.toFinset ⊆ T) :
    nop n F r π σ = ∑ l ∈ S, bet n l * cre l (F (r - l)) π σ + ∑ k ∈ T, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ := by sorry
