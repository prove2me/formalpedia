-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_up_bij
-- name    : Formalism.FourierDecayAlt.P.A5x8.sec_up_bij
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:27.957993+00:00
-- url     : https://prove2.me/theorems/a74b85fc-55ec-41e7-b772-1f6a677c8b16
-- title:
--   A5x8: sec up bij
-- statement:
--   The A5x8 construction uses the sec up bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L717-L770
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L717-L770

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

theorem Formalism.FourierDecayAlt.P.A5x8.sec_up_bij (h : Point K) (c : Kˣ) :
    Function.Bijective (fun p : (upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum)) ×
        (Fin h.1.sum → KR R) =>
      ((sec_upJ h c p.1.out (outV R p.2) : upUniG K (addBlock h 1 c).1.sum) :
        upUniG K (addBlock h 1 c).1.sum ⧸ intSub R (upUniG K (addBlock h 1 c).1.sum))) := by sorry
