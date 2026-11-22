-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_sum_comp
-- name    : Formalism.InvariantFactorPaths.G7.CSym.sum_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:28.379145+00:00
-- url     : https://prove2.me/theorems/a6376c3b-0a23-46e6-996b-2b342b121ad4
-- title:
--   CSym: sum comp
-- statement:
--   The CSym construction uses the sum comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L91-L95

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
open Formalism.InvariantFactorPaths.G7.CSym

theorem Formalism.InvariantFactorPaths.G7.CSym.sum_comp {K A B C ι : Type} [CommRing K] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C] (s : Finset ι) (f : ι → B →ₗ[K] C) (g : A →ₗ[K] B) :
    (∑ i ∈ s, f i).comp g = ∑ i ∈ s, (f i).comp g := by sorry
