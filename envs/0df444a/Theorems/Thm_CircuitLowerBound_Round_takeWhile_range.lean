-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_takeWhile_range
-- name    : CircuitLowerBound.Round.takeWhile_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:56:28.398453+00:00
-- url     : https://prove2.me/theorems/7a5d8c1e-b245-431c-ab11-a9db25f96cb6
-- title:
--   Round: take While range
-- statement:
--   The first numbers that pass a test, if the test holds below m, fails at m, and m is in the
--   range.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L122-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L122-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Round
import Theorems.Thm_Groundwork_PolyT_takeWhile
attribute [local fun_prop] Groundwork.PolyT.takeWhile


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round

theorem CircuitLowerBound.Round.takeWhile_range {p : ℕ → Bool} {m n : ℕ} (h1 : ∀ i < m, p i = true) (h2 : p m = false) (hmn : m < n) :
    (List.range n).takeWhile p = List.range m := by sorry
