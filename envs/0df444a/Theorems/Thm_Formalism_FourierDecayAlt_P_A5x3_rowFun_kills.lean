-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_rowFun_kills
-- name    : Formalism.FourierDecayAlt.P.A5x3.rowFun_kills
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:42.796804+00:00
-- url     : https://prove2.me/theorems/dc1fcfa7-3a30-4ff0-880d-5d37bae4521c
-- title:
--   A5x3: row Fun kills
-- statement:
--   The A5x3 construction uses the row Fun kills property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L264-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L264-L270

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem Formalism.FourierDecayAlt.P.A5x3.rowFun_kills (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) (a : Fin n) :
    latZ R Z ≤ LinearMap.ker (rowFun R Z a) := by sorry
