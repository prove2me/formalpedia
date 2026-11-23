-- Prove2me | Theorems.Thm_Formalism_REAL_mem_cartanP_iff
-- name    : Formalism.REAL.mem_cartanP_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:25.503361+00:00
-- url     : https://prove2.me/theorems/1fc5017c-e06d-4a11-b467-4ae9efd7d0e3
-- title:
--   REAL: mem cartan P iff
-- statement:
--   The REAL construction uses the mem cartan P iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L86-L94

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

theorem Formalism.REAL.mem_cartanP_iff {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inP ε X ↔ Xᴴ = X ∧ X * Jm ε = -(Jm ε * X) := by sorry
