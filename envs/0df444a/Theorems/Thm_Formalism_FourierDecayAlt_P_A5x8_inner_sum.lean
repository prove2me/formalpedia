-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inner_sum
-- name    : Formalism.FourierDecayAlt.P.A5x8.inner_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:11:07.289799+00:00
-- url     : https://prove2.me/theorems/7100f35e-582a-4653-b3c0-ca5a43af4192
-- title:
--   A5x8: inner sum
-- statement:
--   The A5x8 construction uses the inner sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L1797-L1853
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L1797-L1853

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.FourierDecayAlt.P.A5x8.inner_sum (R : Subring K) (ψ : AddChar K ℂ) (hD : LocalDatum K R ψ) {m m' N N' : ℕ}
    (hN : N = m + 1) (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (c : Kˣ) (h₁ : IsInt R Z₁) (h₂ : IsInt R Z₂)
    (d₁ : IsUnit Z₁.det) (d₂ : IsUnit Z₂.det) :
    ∑ᶠ y, tTerm R ψ hN hN' Z₁ Z₂ (c : K) y = singleBlockInner R ψ Z₁ Z₂ (c : K) := by sorry
