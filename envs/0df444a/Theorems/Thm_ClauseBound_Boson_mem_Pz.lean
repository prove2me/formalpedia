-- Prove2me | Theorems.Thm_ClauseBound_Boson_mem_Pz
-- name    : ClauseBound.Boson.mem_Pz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:46.363784+00:00
-- url     : https://prove2.me/theorems/6a4795ea-622f-425e-9d0c-fa8b11548c1e
-- title:
--   Boson: mem Pz
-- statement:
--   The Boson construction uses the mem Pz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L66-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L66-L79

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

theorem ClauseBound.Boson.mem_Pz {m : ℤ} {τ : Multiset ℕ} : τ ∈ Pz m ↔ (τ.sum : ℤ) = m ∧ 0 ∉ τ := by sorry
