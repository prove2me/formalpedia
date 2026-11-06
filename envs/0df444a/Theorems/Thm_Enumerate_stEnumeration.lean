-- Prove2me | Theorems.Thm_Enumerate_stEnumeration
-- name    : Enumerate.stEnumeration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:43:12.573753+00:00
-- url     : https://prove2.me/theorems/25548eff-5907-48a1-a9de-86d3270e81dd
-- title:
--   Enumerate: st Enumeration
-- statement:
--   **Lemma 4 as an enumeration.** For every ε > 0 there is a constant M(ε) ≥ 1 such that for every
--   3-CNF φ on n variables one can compute, in time 2^{εn} times a polynomial in n, at most 2^{εn}
--   3-CNFs on the same variables, each with at most M(ε)·n clauses, such that φ is satisfiable if and
--   only if at least one of them is (the paper's Lemma 4 states more: every satisfying assignment of φ
--   satisfies exactly one of them).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Enumeration.lean#L113-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Enumeration.lean#L113-L120

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

theorem Enumerate.stEnumeration : StEnumeration := by sorry
