-- Prove2me | Theorems.Thm_Formalism_REAL_f1alg_unit_iff
-- name    : Formalism.REAL.f1alg_unit_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:01.812451+00:00
-- url     : https://prove2.me/theorems/0ba799fe-e66c-47fd-b961-894c4c37ead1
-- title:
--   REAL: f1alg unit iff
-- statement:
--   The REAL construction uses the f1alg unit iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L139-L141

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.f1alg_unit_iff {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ gᴴ * g = 1 := by sorry
