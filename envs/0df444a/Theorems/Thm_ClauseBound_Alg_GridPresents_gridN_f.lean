-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_gridN_f
-- name    : ClauseBound.Alg.GridPresents.gridN_f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:09:27.542537+00:00
-- url     : https://prove2.me/theorems/502e1138-6d31-4849-ae3d-67eb320d56ca
-- title:
--   Grid Presents: grid N f
-- statement:
--   The factor of the parts a ≠ b on the side of a: the tests on the edges between nodes of equal
--   number, times the factors of the rectangles.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L239-L270
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L239-L270

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
variable {P pad p d tr h ℓ y}
variable (P pad p d tr h ℓ y)

theorem ClauseBound.Alg.GridPresents.gridN_f (Rm : Inst (Fin (p * d)) (List Bool)) {a b : Fin (nParts p d tr)} (hab : a ≠ b) {z θ : List Bool}
    (hz : z.length = nMemb p d tr * (p * d) * ℓ) (hθ : θ.length = capG P p d tr h ℓ y a b) :
    (gridN P pad p d tr h ℓ y Rm).f a b z θ =
      (∏ i : Fin (nMemb p d tr), if heG p d ℓ z i (nodeG d tr b i) = block ℓ i θ then 1 else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2, item P pad p d tr h ℓ y a b z θ k.1 k.2 := by sorry
