-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_T1_ge
-- name    : ClauseBound.Part.Lower.T1_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:36.421541+00:00
-- url     : https://prove2.me/theorems/d7e55aaf-2e3c-43ed-a938-cd14a91255be
-- title:
--   Lower: T1 ge
-- statement:
--   Σ_v v·e^{−yv} in closed form is at least 1/y² − 1/4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L133-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L133-L154

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

theorem ClauseBound.Part.Lower.T1_ge {y : ℝ} (hy : 0 < y) : 1 / y ^ 2 - 1 / 4 ≤ Real.exp (-y) / (1 - Real.exp (-y)) ^ 2 := by sorry
