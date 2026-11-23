-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_mem_range_iC
-- name    : Formalism.FourierDecayAlt.P.A5x8.mem_range_iC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:05.149949+00:00
-- url     : https://prove2.me/theorems/1ec74fcd-254c-4645-924c-e01cd37dddbc
-- title:
--   A5x8: mem range i C
-- statement:
--   The A5x8 construction uses the mem range i C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L1548-L1561
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L1548-L1561

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
variable {K : Type} [CommRing K] (R : Subring K) {m : ℕ}

theorem Formalism.FourierDecayAlt.P.A5x8.mem_range_iC (Z : Matrix (Fin m) (Fin m) K) (hd : IsUnit Z.det) (x : Fin m → KR R)
    (hx : ∀ j, (Z *ᵥ outV R x) j ∈ R) : x ∈ Set.range (iC R Z) := by sorry
