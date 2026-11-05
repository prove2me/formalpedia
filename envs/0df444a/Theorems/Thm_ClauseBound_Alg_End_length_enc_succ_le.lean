-- Prove2me | Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
-- name    : ClauseBound.Alg.End.length_enc_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:12:49.827224+00:00
-- url     : https://prove2.me/theorems/89082bb1-8179-4aba-bf1f-2d765eb7416c
-- title:
--   End: length enc succ le
-- statement:
--   The length of the code, plus one, is at most 8·(k·m)².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L115-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L115-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat

theorem ClauseBound.Alg.End.length_enc_succ_le {k n : ℕ} {φ : Sat3.CNF n} (hk : 1 ≤ k) (hm : 1 ≤ φ.length) (hn : n ≤ k * φ.length) :
    (SatM.enc k φ).length + 1 ≤ 8 * (k * φ.length) ^ 2 := by sorry
