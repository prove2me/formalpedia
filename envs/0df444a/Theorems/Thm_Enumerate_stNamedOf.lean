-- Prove2me | Theorems.Thm_Enumerate_stNamedOf
-- name    : Enumerate.stNamedOf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:37:22.234065+00:00
-- url     : https://prove2.me/theorems/a26d7ed4-a1d7-4677-a62c-f23ae675cb73
-- title:
--   Enumerate: st Named Of
-- statement:
--   **Lemma 4 as worded, with the list named, from its three parts**: the machine that prints the
--   list, «what the walk produces is that list», and the enumeration for every parameter that is large
--   enough: for every ε > 0 a constant M(ε) ≥ 1 and, for every 3-CNF φ on n variables, at most 2^{εn}
--   3-CNFs on the same variables, computed in time 2^{εn} times a polynomial in n, …
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Named.lean#L91-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Named.lean#L91-L107

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Enumerate_Defs
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_SparsificationLemma_Mach_Full
import Definitions.Def_SparsificationLemma_Mach_LemSparsification
import Definitions.Def_SparsificationLemma_Mach_Len
import Definitions.Def_SparsificationLemma_Mach_Main
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Enumerate_Named
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo SparsificationLemma.Mach Turing

theorem Enumerate.stNamedOf : StNamedOf := by sorry
