-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_occ_eq
-- name    : ClauseBound.ParityChecks.Shape.occ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:49:28.673723+00:00
-- url     : https://prove2.me/theorems/98f0653d-9cfa-4225-9a49-84c9a02ea8fd
-- title:
--   Shape: occ eq
-- statement:
--   The clauses in which v occurs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L87-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L87-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.Shape.occ_eq (x : Fml) (v : ℕ) : occ x v = x.filter (hasV v) := by sorry
