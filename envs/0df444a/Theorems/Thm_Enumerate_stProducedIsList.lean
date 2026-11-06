-- Prove2me | Theorems.Thm_Enumerate_stProducedIsList
-- name    : Enumerate.stProducedIsList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:08:40.537498+00:00
-- url     : https://prove2.me/theorems/9a350508-5551-4be2-909c-c05e0a2f3b04
-- title:
--   Enumerate: st Produced Is List
-- statement:
--   Line 2 of Algorithm 1: «for each Φ in the list that Lemma 4 computes from φ and ε do». The
--   formulas that the walk produces, in its order, are the list `outTau 3 n τ φ`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Enumeration.lean#L51-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Enumeration.lean#L51-L51

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

theorem Enumerate.stProducedIsList : StProducedIsList := by sorry
