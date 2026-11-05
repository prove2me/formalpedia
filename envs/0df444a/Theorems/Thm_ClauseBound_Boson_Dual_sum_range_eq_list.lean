-- Prove2me | Theorems.Thm_ClauseBound_Boson_Dual_sum_range_eq_list
-- name    : ClauseBound.Boson.Dual.sum_range_eq_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:18:23.503325+00:00
-- url     : https://prove2.me/theorems/e7a69f0a-675a-4a21-b4bd-4e238b47ce93
-- title:
--   Dual: sum range eq list
-- statement:
--   A sum over 0, …, n − 1 as the sum of a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Dual.lean#L29-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Dual.lean#L29-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.Dual
open Finset

theorem ClauseBound.Boson.Dual.sum_range_eq_list (F : ℕ → ℤ) (n : ℕ) : ∑ p ∈ range n, F p = ((List.range n).map F).sum := by sorry
