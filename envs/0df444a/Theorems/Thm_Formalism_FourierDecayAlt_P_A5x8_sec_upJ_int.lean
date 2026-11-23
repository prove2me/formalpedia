-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_upJ_int
-- name    : Formalism.FourierDecayAlt.P.A5x8.sec_upJ_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:21.138746+00:00
-- url     : https://prove2.me/theorems/8e264c11-c3fe-4a31-ada6-49a1418cb1ff
-- title:
--   A5x8: sec up J int
-- statement:
--   The A5x8 construction uses the sec up J int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L695-L715
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L695-L715

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
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x8.sec_upJ_int (h : Point K) (c : Kˣ) (b : upUniG K h.1.sum) (ρ : Fin h.1.sum → K) :
    sec_upJ h c b ρ ∈ intSub R (upUniG K (addBlock h 1 c).1.sum) ↔
      b ∈ intSub R (upUniG K h.1.sum) ∧ ∀ j, ρ j ∈ R := by sorry
