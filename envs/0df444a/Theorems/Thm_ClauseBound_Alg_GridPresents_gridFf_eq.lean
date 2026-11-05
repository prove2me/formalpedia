-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_gridFf_eq
-- name    : ClauseBound.Alg.GridPresents.gridFf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:26:48.038078+00:00
-- url     : https://prove2.me/theorems/5355e4f6-7c0c-4e0b-b8a1-0a3d78df68d6
-- title:
--   Grid Presents: grid Ff eq
-- statement:
--   The factor of the parts a, b on the side of a: the tests on the edges between nodes of equal
--   number, times the factors of the rectangles.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L91-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L91-L104

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet

theorem ClauseBound.Alg.GridPresents.gridFf_eq (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y a b : ℕ) (z θ : List Bool) :
    gridFf P pad p d tr h ℓ y ((a, b), (z, θ)) =
      (∏ i : Fin (nMemb p d tr), if heG p d ℓ z i (nodeG d tr b i) = block ℓ i θ then 1 else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2, item P pad p d tr h ℓ y a b z θ k.1 k.2 := by sorry
