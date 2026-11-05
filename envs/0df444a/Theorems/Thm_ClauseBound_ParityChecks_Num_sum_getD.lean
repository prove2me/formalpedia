-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_sum_getD
-- name    : ClauseBound.ParityChecks.Num.sum_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:44.970183+00:00
-- url     : https://prove2.me/theorems/aaef738f-b558-42ad-a03a-99b6a68e2165
-- title:
--   Num: sum get D
-- statement:
--   A sum over the first entries of a list of checks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L45-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L45-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num

theorem ClauseBound.ParityChecks.Num.sum_getD {M : Type} [AddCommMonoid M] (g : Chk → M) (Ls t : List Chk) :
    ∑ i ∈ range Ls.length, g ((Ls ++ t).getD i []) = (Ls.map g).sum := by sorry
