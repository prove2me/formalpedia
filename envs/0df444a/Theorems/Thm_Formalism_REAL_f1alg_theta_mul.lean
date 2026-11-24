-- Prove2me | Theorems.Thm_Formalism_REAL_f1alg_theta_mul
-- name    : Formalism.REAL.f1alg_theta_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:21:50.319396+00:00
-- url     : https://prove2.me/theorems/1b162bcf-9aaf-48fa-88cb-c97c0b1f8c30
-- title:
--   REAL: f1alg theta mul
-- statement:
--   The REAL construction uses the f1alg theta mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L39-L41

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

theorem Formalism.REAL.f1alg_theta_mul {n : ℕ} (ε : Fin n → Bool) (A B : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (A * B) * Jm ε = (Jm ε * A * Jm ε) * (Jm ε * B * Jm ε) := by sorry
