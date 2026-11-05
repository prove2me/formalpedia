-- Prove2me | Theorems.Thm_ClauseBound_Boson_sum_abs_aFam_le
-- name    : ClauseBound.Boson.sum_abs_aFam_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:54.278949+00:00
-- url     : https://prove2.me/theorems/444c79c4-0edb-43cb-8579-cbe9b7fc0cce
-- title:
--   Boson: sum abs a Fam le
-- statement:
--   The absolute values of the coefficients of a^μ add up to at most 2^{|μ|}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Dual.lean#L71-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Dual.lean#L71-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset

theorem ClauseBound.Boson.sum_abs_aFam_le (μ : List ℕ) : ((aFam μ).map fun c => |c.1|).sum ≤ 2 ^ μ.sum := by sorry
