-- Prove2me | Theorems.Thm_CircuitLowerBound_Parse_gateOfW_gateW
-- name    : CircuitLowerBound.Parse.gateOfW_gateW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:50:13.737005+00:00
-- url     : https://prove2.me/theorems/48d1b8f9-2933-4ce9-a2b5-0124b6a82835
-- title:
--   Parse: gate Of W gate W
-- statement:
--   A gate is read back from its word.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L69-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L69-L78

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

theorem CircuitLowerBound.Parse.gateOfW_gateW {W : ℕ} {g : GateD} (h1 : g.2.1 < 2 ^ W) (h2 : g.2.2 < 2 ^ W) : gateOfW W (gateW W g) = g := by sorry
