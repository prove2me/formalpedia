-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_needLoops_polyT
-- name    : ClauseBound.Alg.CertLevel.needLoops_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:03:18.364195+00:00
-- url     : https://prove2.me/theorems/cc3f80b9-eac0-449d-a798-7bdc4369d415
-- title:
--   Cert Level: need Loops poly T
-- statement:
--   The exponents for the loops of one step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L380-L384
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L380-L384

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.needLoops_polyT {need nP p K Pn quo LN eb d lam : α → ℕ} {thin : α → Bool} (h1 : PolyT need) (h2 : PolyT nP) (h3 : PolyT p) (h4 : PolyT K) (h5 : PolyT Pn)
    (h6 : PolyT quo) (h7 : PolyT LN) (h8 : PolyT eb) (h9 : PolyT d) (h10 : PolyT lam) (h11 : PolyT thin) :
    PolyT fun x => max (max (max (need x) (Nat.size (nP x))) (max (p x * Nat.size (K x)) (Pn x * (quo x + 1))))
      (max ((K x - 1) * LN x) (if thin x = true then max (eb x) (p x ^ 2 * d x * lam x) else 0)) := by sorry
