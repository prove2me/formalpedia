-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Spec_deltaF_eq
-- name    : ClauseBound.Inst.Half.Spec.deltaF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:24.170984+00:00
-- url     : https://prove2.me/theorems/69d00924-7fec-48a9-b61e-6fd55f281fea
-- title:
--   Spec: delta F eq
-- statement:
--   The number of all partitions of 0, …, 4h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfSpec.lean#L47-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfSpec.lean#L47-L48

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

theorem ClauseBound.Inst.Half.Spec.deltaF_eq (h : ℕ) : deltaF h = ∑ E ∈ range (4 * h + 1), Partitions.p E := by sorry
