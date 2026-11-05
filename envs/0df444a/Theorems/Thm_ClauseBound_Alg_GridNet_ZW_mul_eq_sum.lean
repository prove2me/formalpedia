-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_ZW_mul_eq_sum
-- name    : ClauseBound.Alg.GridNet.ZW_mul_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:12:53.10842+00:00
-- url     : https://prove2.me/theorems/331c3768-b4be-4097-8375-65accacb2a8e
-- title:
--   Grid Net: ZW mul eq sum
-- statement:
--   The identity D^|R|·Z = Σ_ι Z_ι of the proof of Theorem A(b), with D the multiplier of the pieces
--   and |R| the number of rectangles, on words.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L294-L300
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L294-L300

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

theorem ClauseBound.Alg.GridNet.ZW_mul_eq_sum (p d ℓ : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) (A : ℕ → Pieces.Four ℓ) (n : ℕ) (D : ℤ)
    (hA : ∀ x y u v, ∑ i ∈ range (n + 1), A i x y u v = D * Pieces.cross x y u v) :
    D ^ nRectG p d * Inst.ZW ℓ [] Rm = ∑ y ∈ range ((n + 1) ^ nRectG p d), termZ p d ℓ Rm A n y := by sorry
