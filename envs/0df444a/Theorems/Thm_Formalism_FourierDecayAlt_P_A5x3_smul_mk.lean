-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_smul_mk
-- name    : Formalism.FourierDecayAlt.P.A5x3.smul_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:55.320343+00:00
-- url     : https://prove2.me/theorems/53b6404f-1f18-4475-ac51-05541bccdd9e
-- title:
--   A5x3: smul mk
-- statement:
--   The A5x3 construction uses the smul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L27-L29

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
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)

theorem Formalism.FourierDecayAlt.P.A5x3.smul_mk (r : R) (x : K) :
    r • (Submodule.Quotient.mk x : KR R) = Submodule.Quotient.mk ((r : K) * x) := by sorry
