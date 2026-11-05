-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_itemG_polyT
-- name    : ClauseBound.Alg.CertGridG.itemG_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:01:15.784202+00:00
-- url     : https://prove2.me/theorems/26c2cd56-079e-4c80-ba10-a3b38f29e29e
-- title:
--   Cert Grid G: item G poly T
-- statement:
--   One factor of the product in `gridFf` is polynomial-time, for a number j given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L369-L376
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L369-L376

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
variable {P : PiecesF} (K : P.Keeps)
include K

theorem ClauseBound.Alg.CertGridG.itemG_polyT {pad : α → U} {p d h ℓ y j : α → ℕ} {tr : α → Bool} {q : α → FQ} (hpad : PolyT pad) (hp : Unary p) (hd : Unary d) (ht : PolyT tr)
    (hh : Unary h) (hℓ : Unary ℓ) (hy : PolyT y) (hq : PolyT q) (hj : Unary j) :
    PolyT fun x => if j x / nMemb (p x) (d x) (tr x) < j x % nMemb (p x) (d x) (tr x) then
      rectG P (pad x) (p x) (d x) (tr x) (h x) (ℓ x) (y x) (q x) (j x / nMemb (p x) (d x) (tr x)) (j x % nMemb (p x) (d x) (tr x)) else 1 := by sorry
