-- Prove2me | Theorems.Thm_Formalism_REAL_frobenius_ball_compact_pos_finite
-- name    : Formalism.REAL.frobenius_ball_compact_pos_finite
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:23:48.499252+00:00
-- url     : https://prove2.me/theorems/d58e4104-7a08-47f2-8ca6-3a9c200afb99
-- title:
--   REAL: frobenius ball compact pos finite
-- statement:
--   The REAL construction uses the frobenius ball compact pos finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ModularCharacterEqOneOnExpHermitian.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ModularCharacterEqOneOnExpHermitian.lean#L42-L57

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped NNReal ENNReal
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.frobenius_ball_compact_pos_finite {n : ℕ} (ε : Fin n → Bool) :
    IsCompact {g : UJ ε | hsG g ≤ (n : ℝ) + 1} ∧ 0 < muG ε {g : UJ ε | hsG g ≤ (n : ℝ) + 1} ∧
      muG ε {g : UJ ε | hsG g ≤ (n : ℝ) + 1} < ⊤ := by sorry
