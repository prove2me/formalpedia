-- Prove2me | Theorems.Thm_ClauseBound_Alg_Grid_cutsOK_of_spec
-- name    : ClauseBound.Alg.Grid.cutsOK_of_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:50:55.373068+00:00
-- url     : https://prove2.me/theorems/d946c3e6-5d4d-438a-bb27-9a2e31236892
-- title:
--   Grid: cuts OK of spec
-- statement:
--   What the networks use of the pieces follows from their specification, when the pad is long
--   enough.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Grid.lean#L29-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Grid.lean#L29-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_ClauseBound_Alg_Grid
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Grid
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet

theorem ClauseBound.Alg.Grid.cutsOK_of_spec {P : PiecesF} {pad : U} {h ℓ : ℕ} (hS : P.Spec h ℓ) (hpad : 2 ^ P.need h ℓ ≤ pad.length) :
    ∃ A : ℕ → Pieces.Four ℓ, (∀ x y u v, ∑ i ∈ range (P.cnt h ℓ), A i x y u v = P.d h ℓ * Pieces.cross x y u v) ∧
      CutsOK P pad h ℓ A := by sorry
