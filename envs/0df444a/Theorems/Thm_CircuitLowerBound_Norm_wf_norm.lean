-- Prove2me | Theorems.Thm_CircuitLowerBound_Norm_wf_norm
-- name    : CircuitLowerBound.Norm.wf_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:43:47.723202+00:00
-- url     : https://prove2.me/theorems/0eb2cdd6-5cd6-42b5-a31c-337d2a137d29
-- title:
--   Norm: wf norm
-- statement:
--   Every gate reads earlier wires only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean#L69-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean#L69-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Norm
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Norm

theorem CircuitLowerBound.Norm.wf_norm (C : Circuit) (n : ℕ) (hn : 1 ≤ n) : WF n (norm n C) := by sorry
