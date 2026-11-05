-- Prove2me | Theorems.Thm_ClauseBound_Alg_End_time_le
-- name    : ClauseBound.Alg.End.time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:48:17.479556+00:00
-- url     : https://prove2.me/theorems/3ed7c691-f69e-4db3-9504-716da116eceb
-- title:
--   End: time le
-- statement:
--   If L + 1 ≤ 8T², T ≤ 2^(H·X) and E ≤ G·X then q·(L + 2^E + 1)^q ≤ C·2^(C·X) with C = q·9^q +
--   q·(2H + G).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L204-L235
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L204-L235

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat

theorem ClauseBound.Alg.End.time_le (q L E T H G : ℕ) {X : ℝ} (hX : 0 ≤ X) (hT1 : 1 ≤ T) (hL : L + 1 ≤ 8 * T ^ 2) (hT : (T : ℝ) ≤ (2 : ℝ) ^ ((H : ℝ) * X))
    (hE : (E : ℝ) ≤ (G : ℝ) * X) :
    ((q * (L + 2 ^ E + 1) ^ q : ℕ) : ℝ) ≤ ((q * 9 ^ q + q * (2 * H + G) : ℕ) : ℝ) * (2 : ℝ) ^ (((q * 9 ^ q + q * (2 * H + G) : ℕ) : ℝ) * X) := by sorry
