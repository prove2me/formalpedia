-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_sinh_le_mul_cosh
-- name    : ClauseBound.Part.Lower.sinh_le_mul_cosh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:28.812625+00:00
-- url     : https://prove2.me/theorems/9a770083-ffaa-4996-a4d1-8b7137003f85
-- title:
--   Lower: sinh le mul cosh
-- statement:
--   sinh z ≤ z·cosh z for z ≥ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L99-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L99-L107

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower

theorem ClauseBound.Part.Lower.sinh_le_mul_cosh {z : ℝ} (hz : 0 ≤ z) : Real.sinh z ≤ z * Real.cosh z := by sorry
