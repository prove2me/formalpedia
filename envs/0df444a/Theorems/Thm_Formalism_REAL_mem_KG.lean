-- Prove2me | Theorems.Thm_Formalism_REAL_mem_KG
-- name    : Formalism.REAL.mem_KG
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:56.743525+00:00
-- url     : https://prove2.me/theorems/33fa0206-b184-4811-9bf3-938c767cdfb7
-- title:
--   REAL: mem KG
-- statement:
--   The REAL construction uses the mem KG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/SmoothOnGVIff.lean#L64-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/SmoothOnGVIff.lean#L64-L64

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

theorem Formalism.REAL.mem_KG {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) : g ∈ KG ε ↔ toM g ∈ Kset ε := by sorry
