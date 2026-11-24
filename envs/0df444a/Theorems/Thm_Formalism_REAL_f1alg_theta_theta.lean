-- Prove2me | Theorems.Thm_Formalism_REAL_f1alg_theta_theta
-- name    : Formalism.REAL.f1alg_theta_theta
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:06.709398+00:00
-- url     : https://prove2.me/theorems/c9f9812d-fdca-4758-aa93-5834f1869a26
-- title:
--   REAL: f1alg theta theta
-- statement:
--   The REAL construction uses the f1alg theta theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L43-L45

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

theorem Formalism.REAL.f1alg_theta_theta {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * A * Jm ε) * Jm ε = A := by sorry
