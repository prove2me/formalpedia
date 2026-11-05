-- Prove2me | Theorems.Thm_ClauseBound_Boson_Size_sum_mul_count
-- name    : ClauseBound.Boson.Size.sum_mul_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:38:11.544287+00:00
-- url     : https://prove2.me/theorems/378888a9-b8ea-4c1f-809a-1fe09daf2980
-- title:
--   Size: sum mul count
-- statement:
--   The weight of a monomial is the sum of k·(number of parts equal to k).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L56-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L56-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Rec_Window
import Definitions.Def_ClauseBound_Boson_Size
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Size

theorem ClauseBound.Boson.Size.sum_mul_count (σ : Multiset ℕ) : ∑ k ∈ σ.toFinset, (k : ℤ) * (σ.count k : ℤ) = (σ.sum : ℤ) := by sorry
