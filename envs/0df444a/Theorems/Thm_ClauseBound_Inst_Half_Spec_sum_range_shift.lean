-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Spec_sum_range_shift
-- name    : ClauseBound.Inst.Half.Spec.sum_range_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:37.790542+00:00
-- url     : https://prove2.me/theorems/f7c8cf2b-1ddb-456b-a2ea-a8fd0eef4859
-- title:
--   Spec: sum range shift
-- statement:
--   A sum over i = 0, …, 4h of a function of i − 2h is the sum over −2h, …, 2h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfSpec.lean#L28-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfSpec.lean#L28-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfSpec
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open ClauseBound.Inst.Half.Spec

theorem ClauseBound.Inst.Half.Spec.sum_range_shift (h : ℕ) (f : ℤ → ℤ) : ∑ i ∈ range (4 * h + 1), f ((i : ℤ) - 2 * h) = ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), f s := by sorry
