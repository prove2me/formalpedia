-- Prove2me | Theorems.Thm_CliqueLevels_Proof_bound_mono
-- name    : CliqueLevels.Proof.bound_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:43:47.335108+00:00
-- url     : https://prove2.me/theorems/e37180a6-d212-4d38-b526-b7efb4291909
-- title:
--   Proof: bound mono
-- statement:
--   The bound grows with the constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevels.lean#L145-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/GenLevels.lean#L145-L146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_GenLevelsDefs
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Closure_Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_GenLevels
set_option autoImplicit false
section
section
open CliqueLevels CliqueLevels.Proof
open Groundwork Printed

theorem CliqueLevels.Proof.bound_mono {e : ℝ} {K C₀ C₁ lam B : ℕ} (hK : 1 ≤ K) (hl : 1 ≤ lam) (h : C₀ ≤ C₁) : bound e K C₀ lam B ≤ bound e K C₁ lam B := by sorry
