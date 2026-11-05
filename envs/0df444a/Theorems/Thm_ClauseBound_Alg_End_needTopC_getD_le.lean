-- Prove2me | Theorems.Thm_ClauseBound_Alg_End_needTopC_getD_le
-- name    : ClauseBound.Alg.End.needTopC_getD_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:45:18.55391+00:00
-- url     : https://prove2.me/theorems/7958f876-b48d-4ed5-a2f9-62ad14b3d349
-- title:
--   End: need Top C get D le
-- statement:
--   The exponent computed under the bound b, or else b, is at most b and at most the exponent of the
--   clique algorithm.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L49-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L49-L72

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

theorem ClauseBound.Alg.End.needTopC_getD_le {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) (b : U) (i : Idx) (k m : ℕ) :
    (needTopC S b i k m).getD b.length ≤ b.length ∧ (needTopC S b i k m).getD b.length ≤ needTop S i k m := by sorry
