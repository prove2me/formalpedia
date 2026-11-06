-- Prove2me | Theorems.Thm_Enumerate_stSameTree
-- name    : Enumerate.stSameTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:05:29.028077+00:00
-- url     : https://prove2.me/theorems/ff38a7e8-c989-401e-b870-0a274c4003f5
-- title:
--   Enumerate: st Same Tree
-- statement:
--   The walk that produces the outputs ψ ∪ 𝒩 and the walk of
--   `SparsificationLemma.TreeWalk.lemSparsification_walk`, which tests ψ, go through the same tree: the
--   rule never looks at the side list 𝒩 (`SparsificationLemma.stUnchanged`). This ties the enumeration
--   to the form of Lemma 4 that `SparsificationLemma.TreeWalk.lemSparsification_walk` treats; no
--   sentence of the paper corresponds to it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Enumeration.lean#L58-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Enumeration.lean#L58-L58

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

theorem Enumerate.stSameTree : StSameTree := by sorry
