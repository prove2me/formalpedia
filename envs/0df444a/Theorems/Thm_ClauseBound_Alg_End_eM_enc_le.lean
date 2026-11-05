-- Prove2me | Theorems.Thm_ClauseBound_Alg_End_eM_enc_le
-- name    : ClauseBound.Alg.End.eM_enc_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:10:45.375208+00:00
-- url     : https://prove2.me/theorems/031405bd-60b8-4391-b191-bbf2094a8dca
-- title:
--   End: e M enc le
-- statement:
--   On the code of (k, φ) the exponent is at most n and at most the exponent of the clique algorithm
--   at the level picked for m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L76-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L76-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat

theorem ClauseBound.Alg.End.eM_enc_le {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (pick : U → U × Idx) {k n : ℕ} {φ : Sat3.CNF n} (hk : 1 ≤ k)
    (hφ : ∀ C ∈ φ, C.length ≤ k) :
    eM S pick (SatM.enc k φ) ≤ n ∧ eM S pick (SatM.enc k φ) ≤ needTop S (pick (root9 φ.length)).2 k φ.length := by sorry
