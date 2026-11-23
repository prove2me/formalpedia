-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iota_injective
-- name    : Formalism.FourierDecayAlt.P.A5x8.iota_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:54.259227+00:00
-- url     : https://prove2.me/theorems/136f92de-1d18-4416-accd-51182e81f9c5
-- title:
--   A5x8: iota injective
-- statement:
--   The A5x8 construction uses the iota injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L1712-L1719
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L1712-L1719

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
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.A5x8.iota_injective (R : Subring K) {m m' : ℕ} (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (h₁ : IsInt R Z₁) (h₂ : IsInt R Z₂) (d₁ : IsUnit Z₁.det)
    (d₂ : IsUnit Z₂.det) : Function.Injective (iota R Z₁ Z₂) := by sorry
