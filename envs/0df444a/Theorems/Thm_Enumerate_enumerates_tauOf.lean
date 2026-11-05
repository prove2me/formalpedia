-- Prove2me | Theorems.Thm_Enumerate_enumerates_tauOf
-- name    : Enumerate.enumerates_tauOf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:08:06.793837+00:00
-- url     : https://prove2.me/theorems/51578025-5c18-4a99-b97f-0d6d19d40881
-- title:
--   Enumerate: enumerates tau Of
-- statement:
--   The parameter τ = 2^(4s+17) is large enough for ε as soon as s ≥ `s0U 3` and C/ε ≤ 2^s for some
--   C ≥ 1; so, by the enumeration for every parameter that is large enough, the walk with this parameter
--   is an enumeration for ε with M(ε) = τ⁶. (Lemma 4: «For every ε > 0 there is a constant M(ε) ≥ 1 such
--   that …».)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Named.lean#L58-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Named.lean#L58-L69

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

theorem Enumerate.enumerates_tauOf (hE : StEnumeratesTau) {ε : ℝ} {C s : ℕ} (h0 : 0 < ε) (hC : 1 ≤ C) (hs0 : s0U 3 ≤ s) (hs : (C : ℝ) / ε ≤ (2 : ℝ) ^ s) :
    Enumerates ε (tauOf s ^ 6) (tauOf s) := by sorry
