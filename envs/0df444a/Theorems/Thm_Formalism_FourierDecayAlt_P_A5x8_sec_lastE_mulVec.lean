-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lastE_mulVec
-- name    : Formalism.FourierDecayAlt.P.A5x8.sec_lastE_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:13.209291+00:00
-- url     : https://prove2.me/theorems/36d27b63-7a4f-4dcb-9b4d-3856f3088ed5
-- title:
--   A5x8: sec last E mul Vec
-- statement:
--   The A5x8 construction uses the sec last E mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L319-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L319-L336

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] {m N : ℕ}

theorem Formalism.FourierDecayAlt.P.A5x8.sec_lastE_mulVec {u : Matrix (Fin m) (Fin m) K} (hu : IsUpUni u) (η : Fin m → K) :
    lastE (u *ᵥ η) = lastE η := by sorry
