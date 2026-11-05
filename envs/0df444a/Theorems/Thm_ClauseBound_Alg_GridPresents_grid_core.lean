-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_grid_core
-- name    : ClauseBound.Alg.GridPresents.grid_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:51:12.894228+00:00
-- url     : https://prove2.me/theorems/23870f26-7b9d-4dca-ba5c-6f8f677df9ea
-- title:
--   Grid Presents: grid core
-- statement:
--   Both factors of two parts a < b at once: o is the other part, and top says whether the function
--   `top` or the function `bot` of the factorizations in `cutsG` is taken.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L190-L233
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L190-L233

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

theorem ClauseBound.Alg.GridPresents.grid_core (top : Bool) (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b)
    (o : Fin (nParts p d tr)) {z θ : List Bool} (hz : z.length = nMemb p d tr * (p * d) * ℓ)
    (hθ : θ.length = nMemb p d tr * ℓ + ∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ) :
    (if θ ∈ (gridCl P pad p d tr h ℓ y R a b).D then
      (∏ i : Fin (nMemb p d tr), if (stC p d tr ℓ).dec z i (o, i) = ((gridCl P pad p d tr h ℓ y R a b).dec θ).1 i then (1 : ℤ) else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2,
        if top = true then
          (cutsG P pad p d tr h ℓ y ((a, b), k)).top ((stC p d tr ℓ).dec z k.1 (o, k.2)) ((stC p d tr ℓ).dec z k.2 (o, k.1))
            (((gridCl P pad p d tr h ℓ y R a b).dec θ).2 k)
        else
          (cutsG P pad p d tr h ℓ y ((a, b), k)).bot ((stC p d tr ℓ).dec z k.1 (o, k.2)) ((stC p d tr ℓ).dec z k.2 (o, k.1))
            (((gridCl P pad p d tr h ℓ y R a b).dec θ).2 k)
      else 0) =
      (∏ i : Fin (nMemb p d tr), if heG p d ℓ z i (nodeG d tr o i) = block ℓ i θ then 1 else 0) *
      ∏ k : Fin (nMemb p d tr) × Fin (nMemb p d tr) with k.1 < k.2,
        (if top = true then P.top else P.bot) ((pad, tr), (h, digG P d tr h ℓ y (tri a b) (tri k.1 k.2)),
          (heG p d ℓ z k.1 (nodeG d tr o k.2), heG p d ℓ z k.2 (nodeG d tr o k.1),
            chunkAt (lenG P d tr h ℓ y (tri a b)) (tri k.1 k.2) (θ.drop (nMemb p d tr * ℓ)))) := by sorry
