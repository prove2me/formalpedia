-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_comp_sum
-- name    : Formalism.InvariantFactorPaths.G7.CSym.comp_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:09.709766+00:00
-- url     : https://prove2.me/theorems/5fb88671-e029-4c9f-a2e9-00c7afc55351
-- title:
--   CSym: comp sum
-- statement:
--   The CSym construction uses the comp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L97-L101

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

theorem Formalism.InvariantFactorPaths.G7.CSym.comp_sum {K A B C ι : Type} [CommRing K] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C] (s : Finset ι) (f : ι → A →ₗ[K] B) (g : B →ₗ[K] C) :
    g.comp (∑ i ∈ s, f i) = ∑ i ∈ s, g.comp (f i) := by sorry
