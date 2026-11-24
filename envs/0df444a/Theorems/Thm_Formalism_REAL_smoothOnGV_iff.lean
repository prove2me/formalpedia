-- Prove2me | Theorems.Thm_Formalism_REAL_smoothOnGV_iff
-- name    : Formalism.REAL.smoothOnGV_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:41:49.627611+00:00
-- url     : https://prove2.me/theorems/acac607e-37b9-4d5b-83b8-d82f0c25da18
-- title:
--   REAL: smooth On GV iff
-- statement:
--   The REAL construction uses the smooth On GV iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/SmoothOnGVIff.lean#L177-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/SmoothOnGVIff.lean#L177-L178

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementD
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.REAL.smoothOnGV_iff {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    SmoothOnGV ε f ↔ SmoothOnG ε f := by sorry
