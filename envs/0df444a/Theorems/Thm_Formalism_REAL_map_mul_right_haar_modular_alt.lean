-- Prove2me | Theorems.Thm_Formalism_REAL_map_mul_right_haar_modular_alt
-- name    : Formalism.REAL.map_mul_right_haar_modular_alt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:23:17.021079+00:00
-- url     : https://prove2.me/theorems/f0ab8ba6-d7c7-4fee-991a-f38a4f304f4d
-- title:
--   REAL: map mul right haar modular alt
-- statement:
--   The REAL construction uses the map mul right haar modular alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ModularCharacterEqOneOnExpHermitian.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ModularCharacterEqOneOnExpHermitian.lean#L27-L30

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

theorem Formalism.REAL.map_mul_right_haar_modular_alt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) :
    Measure.map (fun x => x * g) (muG ε) = modularCharacterAlt ε g • muG ε := by sorry
