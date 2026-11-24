-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_gauss_elementary_symmetric
-- name    : Formalism.InvariantFactorPaths.G7.gauss_elementary_symmetric
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:43.211883+00:00
-- url     : https://prove2.me/theorems/fd0bea8c-b4ef-4f0f-81da-92936d40325f
-- title:
--   G7: gauss elementary symmetric
-- statement:
--   The G7 construction uses the gauss elementary symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L161-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L161-L168

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open CSym

theorem Formalism.InvariantFactorPaths.G7.gauss_elementary_symmetric : GaussEsymm := by sorry
