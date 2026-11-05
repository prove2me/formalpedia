-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_length_occ_incL
-- name    : ClauseBound.ParityChecks.Shape.length_occ_incL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:51:21.640654+00:00
-- url     : https://prove2.me/theorems/3f5eb4da-46d9-44db-8412-f37ccd0777a8
-- title:
--   Shape: length occ inc L
-- statement:
--   The incidences in which v occurs, check by check.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L211-L220
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L211-L220

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
variable {k n Δ : ℕ} {q : Par} {ψ : Fml} {Lam : List Chk} {j : ℕ}

theorem ClauseBound.ParityChecks.Shape.length_occ_incL (n : ℕ) (ψ : Fml) (Lam : List Chk) (j v : ℕ) : (occ (incL n ψ Lam j) v).length =
    ∑ j' ∈ range j, (Lam.getD j' []).countP (fun x => hasV v (ψ.getD x [] ++ [(n + j', false)])) +
      (Lam.getD j []).countP fun x => hasV v (ψ.getD x []) := by sorry
