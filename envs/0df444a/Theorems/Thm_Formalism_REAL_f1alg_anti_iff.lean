-- Prove2me | Theorems.Thm_Formalism_REAL_f1alg_anti_iff
-- name    : Formalism.REAL.f1alg_anti_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:51:55.001973+00:00
-- url     : https://prove2.me/theorems/ea7bb46d-b2b1-4aea-b76d-456cfbebca41
-- title:
--   REAL: f1alg anti iff
-- statement:
--   The REAL construction uses the f1alg anti iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L56-L63

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

theorem Formalism.REAL.f1alg_anti_iff {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * Jm ε = -(Jm ε * A) ↔ Jm ε * A * Jm ε = -A := by sorry
