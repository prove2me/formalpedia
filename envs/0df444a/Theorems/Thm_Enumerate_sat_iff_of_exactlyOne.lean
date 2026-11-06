-- Prove2me | Theorems.Thm_Enumerate_sat_iff_of_exactlyOne
-- name    : Enumerate.sat_iff_of_exactlyOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:07:50.965119+00:00
-- url     : https://prove2.me/theorems/07bd8ba1-dc81-462c-af95-262c2eb8bcd8
-- title:
--   Enumerate: sat iff of exactly One
-- statement:
--   φ is satisfiable if and only if at least one of them is, from the property that every assignment
--   that satisfies φ satisfies exactly one formula of the list, and no other assignment any.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Enumeration.lean#L80-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Enumeration.lean#L80-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Enumerate_Defs
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_SparsificationLemma_Geo_Eps
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_Enumerate_Enumeration
set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo

theorem Enumerate.sat_iff_of_exactlyOne {φ : PFml} {L : List PFml} (h : ∀ b, ExactlyOne b φ L) : (∃ b, SparsificationLemma.Sat b φ) ↔ ∃ Φ ∈ L, ∃ b, SparsificationLemma.Sat b Φ := by sorry
