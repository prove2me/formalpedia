-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_orbZ
-- name    : Formalism.FourierDecayAlt.P.A5x8.sec_orbZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:28.820467+00:00
-- url     : https://prove2.me/theorems/a4d58581-345e-4674-849d-6515afd8e4ec
-- title:
--   A5x8: sec orb Z
-- statement:
--   The A5x8 construction uses the sec orb Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L414-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L414-L425

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_addBlock_sum

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
variable {K : Type} [CommRing K]
variable {m N : ℕ}

theorem Formalism.FourierDecayAlt.P.A5x8.sec_orbZ (h : Point K) (c : Kˣ) (p : lowW K h.1 h.2 × upUniG K h.1.sum)
    (ξ η : Fin h.1.sum → K) :
    orbZ (addBlock h 1 c) (sec_lowJ h c p.1 ξ, sec_upJ h c p.2 η) =
      bigZ (addBlock_sum h c) (orbZ h p) ξ η (c : K) := by sorry
