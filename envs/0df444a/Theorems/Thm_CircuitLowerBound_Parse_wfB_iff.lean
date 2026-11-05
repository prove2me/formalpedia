-- Prove2me | Theorems.Thm_CircuitLowerBound_Parse_wfB_iff
-- name    : CircuitLowerBound.Parse.wfB_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:51:28.415702+00:00
-- url     : https://prove2.me/theorems/2b45911d-130a-429a-8510-9cdcfb98c4eb
-- title:
--   Parse: wf B iff
-- statement:
--   The test is right.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L117-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L117-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Parse
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Parse

theorem CircuitLowerBound.Parse.wfB_iff (n : ℕ) (C : List GateD) : wfB n C = true ↔ WF n C := by sorry
