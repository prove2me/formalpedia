-- Prove2me | Theorems.Thm_ClauseBound_Part_Upper_exp_div_le
-- name    : ClauseBound.Part.Upper.exp_div_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:01.901071+00:00
-- url     : https://prove2.me/theorems/1d5d1755-acf6-4500-bd06-2a214e607a2c
-- title:
--   Upper: exp div le
-- statement:
--   e^{−y}/(1 − e^{−y})² ≤ 1/y² for y > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Upper.lean#L50-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Upper.lean#L50-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Upper
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Upper

theorem ClauseBound.Part.Upper.exp_div_le {y : ℝ} (hy : 0 < y) : Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 ≤ 1 / y ^ 2 := by sorry
