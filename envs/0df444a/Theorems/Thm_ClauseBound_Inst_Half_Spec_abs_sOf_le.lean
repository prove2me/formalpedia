-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Spec_abs_sOf_le
-- name    : ClauseBound.Inst.Half.Spec.abs_sOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:20.110508+00:00
-- url     : https://prove2.me/theorems/545e5604-defd-49ba-b337-f739d9cec529
-- title:
--   Spec: abs s Of le
-- statement:
--   |s| ≤ 2h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfSpec.lean#L51-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfSpec.lean#L51-L53

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

theorem ClauseBound.Inst.Half.Spec.abs_sOf_le (h i : ℕ) : |sOf h i| ≤ 2 * (h : ℤ) := by sorry
