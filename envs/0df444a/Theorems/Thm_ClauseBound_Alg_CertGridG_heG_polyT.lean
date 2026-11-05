-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_heG_polyT
-- name    : ClauseBound.Alg.CertGridG.heG_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:14:58.414891+00:00
-- url     : https://prove2.me/theorems/b821fded-73e6-401c-9c22-3bc7ce580ce7
-- title:
--   Cert Grid G: he G poly T
-- statement:
--   A half-edge in the word of a state is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L146-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L146-L148

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]

theorem ClauseBound.Alg.CertGridG.heG_polyT {p d ℓ i u : α → ℕ} {z : α → List Bool} (hp : PolyT p) (hd : PolyT d) (hℓ : PolyT ℓ) (hz : PolyT z) (hi : PolyT i)
    (hu : PolyT u) : PolyT fun x => heG (p x) (d x) (ℓ x) (z x) (i x) (u x) := by sorry
