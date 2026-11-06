-- Prove2me | Theorems.Thm_CircuitLowerBound_Parse_length_encC
-- name    : CircuitLowerBound.Parse.length_encC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:49:44.778199+00:00
-- url     : https://prove2.me/theorems/19bc949c-a991-4c82-b0d8-85a2ae34a387
-- title:
--   Parse: length enc C
-- statement:
--   The length of the code.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L101-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L101-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Parse

theorem CircuitLowerBound.Parse.length_encC (W : ℕ) (C : List GateD) : (encC W C).length = W + 1 + C.length * (4 + 2 * W) := by sorry
