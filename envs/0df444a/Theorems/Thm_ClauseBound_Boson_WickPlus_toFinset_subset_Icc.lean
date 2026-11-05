-- Prove2me | Theorems.Thm_ClauseBound_Boson_WickPlus_toFinset_subset_Icc
-- name    : ClauseBound.Boson.WickPlus.toFinset_subset_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:38:00.560186+00:00
-- url     : https://prove2.me/theorems/49ed6a2c-7140-4cc9-bdda-300f5a91c759
-- title:
--   Wick Plus: to Finset subset Icc
-- statement:
--   The parts of a monomial of weight at most M lie between 1 and M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/WickPlus.lean#L24-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/WickPlus.lean#L24-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_WickPlus
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.WickPlus
open Finset

theorem ClauseBound.Boson.WickPlus.toFinset_subset_Icc {τ : Multiset ℕ} (h0 : 0 ∉ τ) {M : ℕ} (hM : τ.sum ≤ M) : τ.toFinset ⊆ Icc 1 M := by sorry
