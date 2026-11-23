-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_section_exists
-- name    : Formalism.FourierDecayAlt.P.A5x8.section_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:47.562381+00:00
-- url     : https://prove2.me/theorems/b2397a3b-9ab2-48fa-84f5-e599730bbeb2
-- title:
--   A5x8: section exists
-- statement:
--   The A5x8 construction uses the section exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L784-L792
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L784-L792

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_section_exists
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
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x8.section_exists (h : Point K) (c : Kˣ) :
    ∃ σ : Par R h → lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 × upUniG K (addBlock h 1 c).1.sum,
      Function.Bijective (fun t => toCos R (σ t)) ∧
      ∀ t, orbZ (addBlock h 1 c) (σ t) =
          bigZ (addBlock_sum h c) (orbZ h (rep R t.1)) (outV R t.2.1) (outV R t.2.2) (c : K) ∧
        ∀ ψ : AddChar K ℂ, phase ψ (σ t) =
          phase ψ (rep R t.1) * ψ (lastE (outV R t.2.1) + lastE (outV R t.2.2)) := by sorry
