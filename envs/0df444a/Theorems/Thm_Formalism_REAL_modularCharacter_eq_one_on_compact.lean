-- Prove2me | Theorems.Thm_Formalism_REAL_modularCharacter_eq_one_on_compact
-- name    : Formalism.REAL.modularCharacter_eq_one_on_compact
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:01.424821+00:00
-- url     : https://prove2.me/theorems/2af1b179-3528-4022-8c7c-d9256004ff4f
-- title:
--   REAL: modular Character eq one on compact
-- statement:
--   The REAL construction uses the modular Character eq one on compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ModularCharacterEqOneOnExpHermitian.lean#L59-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ModularCharacterEqOneOnExpHermitian.lean#L59-L75

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

theorem Formalism.REAL.modularCharacter_eq_one_on_compact {n : ℕ} (ε : Fin n → Bool) (g : UJ ε)
    (hk : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    modularCharacterAlt ε g = 1 := by sorry
