-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_finsum_of_inj
-- name    : Formalism.FourierDecayAlt.P.A5x8.finsum_of_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:40.991163+00:00
-- url     : https://prove2.me/theorems/8ecb461e-bc50-4160-ac94-41b8f4ace931
-- title:
--   A5x8: finsum of inj
-- statement:
--   The A5x8 construction uses the finsum of inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L1673-L1678
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelExplicitFormula.lean#L1673-L1678

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

theorem Formalism.FourierDecayAlt.P.A5x8.finsum_of_inj {X S : Type} (ι : S → X) (hι : Function.Injective ι) (t : X → ℂ)
    (ht : Function.support t ⊆ Set.range ι) : ∑ᶠ x, t x = ∑ᶠ s, t (ι s) := by sorry
