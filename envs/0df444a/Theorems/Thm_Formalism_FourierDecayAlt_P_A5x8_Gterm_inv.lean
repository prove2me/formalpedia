-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_Gterm_inv
-- name    : Formalism.FourierDecayAlt.P.A5x8.Gterm_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:33.541346+00:00
-- url     : https://prove2.me/theorems/d3147943-a931-4bb0-926e-95127b8f8483
-- title:
--   A5x8: Gterm inv
-- statement:
--   The A5x8 construction uses the Gterm inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L868-L885
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L868-L885

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

theorem Formalism.FourierDecayAlt.P.A5x8.Gterm_inv (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w w' : Point K)
    (p p₁ : lowW K w.1 w.2 × upUniG K w.1.sum) (p' p₁' : lowW K w'.1 w'.2 × upUniG K w'.1.sum)
    (h : toCos R p = toCos R p₁) (h' : toCos R p' = toCos R p₁') :
    Gterm R ψ w w' p p' = Gterm R ψ w w' p₁ p₁' := by sorry
