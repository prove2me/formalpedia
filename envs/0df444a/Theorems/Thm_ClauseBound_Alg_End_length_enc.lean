-- Prove2me | Theorems.Thm_ClauseBound_Alg_End_length_enc
-- name    : ClauseBound.Alg.End.length_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:35:43.118989+00:00
-- url     : https://prove2.me/theorems/b1bbc033-4b1d-44e1-8136-d8e706f23167
-- title:
--   End: length enc
-- statement:
--   The code of (k, φ) has k + n + 2 + m·k·(⌊log₂ 2n⌋ + 1) symbols.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L85-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L85-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat

theorem ClauseBound.Alg.End.length_enc (k : ℕ) {n : ℕ} (φ : Sat3.CNF n) :
    (SatM.enc k φ).length = k + n + 2 + φ.length * (k * (Nat.log2 (2 * n) + 1)) := by sorry
