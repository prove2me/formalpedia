-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_int
-- name    : Formalism.FourierDecayAlt.P.A5x8.sec_lowJ_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:26.495512+00:00
-- url     : https://prove2.me/theorems/8c291972-8e05-4b67-a83f-82b903f07b6c
-- title:
--   A5x8: sec low J int
-- statement:
--   The A5x8 construction uses the sec low J int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L578-L598
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L578-L598

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

theorem Formalism.FourierDecayAlt.P.A5x8.sec_lowJ_int (h : Point K) (c : Kˣ) (a : lowW K h.1 h.2) (ρ : Fin h.1.sum → K) :
    sec_lowJ h c a ρ ∈ intSub R (lowW K (addBlock h 1 c).1 (addBlock h 1 c).2) ↔
      a ∈ intSub R (lowW K h.1 h.2) ∧ ∀ j, ρ j ∈ R := by sorry
