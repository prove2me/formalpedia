-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_low_bij
-- name    : Formalism.FourierDecayAlt.P.A5x8.sec_low_bij
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:44.959735+00:00
-- url     : https://prove2.me/theorems/dbca79a9-2810-40bf-befa-e94a9fa1149f
-- title:
--   A5x8: sec low bij
-- statement:
--   The A5x8 construction uses the sec low bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L600-L642
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L600-L642

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

theorem Formalism.FourierDecayAlt.P.A5x8.sec_low_bij (h : Point K) (c : Kˣ) :
    Function.Bijective (fun p : Quotient (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2))) ×
        (Fin h.1.sum → KR R) =>
      (Quotient.mk (QuotientGroup.rightRel
        (intSub R (lowW K (addBlock h 1 c).1 (addBlock h 1 c).2)))
        (sec_lowJ h c p.1.out (outV R p.2)))) := by sorry
