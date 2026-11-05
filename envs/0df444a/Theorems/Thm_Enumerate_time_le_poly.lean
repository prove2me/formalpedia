-- Prove2me | Theorems.Thm_Enumerate_time_le_poly
-- name    : Enumerate.time_le_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:08:01.948698+00:00
-- url     : https://prove2.me/theorems/6d71d228-c813-44fa-842f-4b6cf25b9d05
-- title:
--   Enumerate: time le poly
-- statement:
--   «in time 2^{εn} times a polynomial in n»: the bound C₀·(length of the input + 8)^C₀·2^(C₀·⌊n/2^s⌋)
--   of the machine is at most 2^{εn}·c(n+1)^c with c = C₀·(s+412)^C₀ + 4C₀, if C₀ ≤ C and C/ε ≤ 2^s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Named.lean#L73-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Named.lean#L73-L85

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo SparsificationLemma.Mach Turing

theorem Enumerate.time_le_poly {C₀ C n s : ℕ} {φ : Sat3.CNF n} {ε : ℝ} (h3 : SatK.IsKCNF 3 φ) (hc : C₀ ≤ C) (h0 : 0 < ε) (hs : (C : ℝ) / ε ≤ (2 : ℝ) ^ s) :
    ((C₀ * ((encIn s 3 φ).length + 2 ^ 3) ^ C₀ * 2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ (ε * (n : ℝ)) * (((C₀ * (s + 412) ^ C₀ + 4 * C₀ : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C₀ * (s + 412) ^ C₀ + 4 * C₀)) := by sorry
