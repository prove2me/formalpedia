-- Prove2me | Theorems.Thm_Formalism_REAL_mem_unitaryGroup_iff_mul_conjTranspose
-- name    : Formalism.REAL.mem_unitaryGroup_iff_mul_conjTranspose
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:23:28.669354+00:00
-- url     : https://prove2.me/theorems/41c00ca4-8011-408a-ad64-b148aff9ae3b
-- title:
--   REAL: mem unitary Group iff mul conj Transpose
-- statement:
--   The REAL construction uses the mem unitary Group iff mul conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L143-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L143-L145

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

theorem Formalism.REAL.mem_unitaryGroup_iff_mul_conjTranspose {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ g * gᴴ = 1 := by sorry
