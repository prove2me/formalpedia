-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_conv_smul
-- name    : Formalism.InvariantFactorPaths.G7.CSym.conv_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:14.720192+00:00
-- url     : https://prove2.me/theorems/a7e066df-6a84-4635-8c3d-51f73767bdbc
-- title:
--   CSym: conv smul
-- statement:
--   The CSym construction uses the conv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L76-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L76-L89

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

theorem Formalism.InvariantFactorPaths.G7.CSym.conv_smul {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] (f g : ℕ → K) (E : ℕ → V)
    (i : ℕ) :
    ∑ l ∈ range (i + 1), f l • ∑ l' ∈ range (i - l + 1), g l' • E (i - l - l') =
      ∑ n ∈ range (i + 1), (∑ a ∈ range (n + 1), f a * g (n - a)) • E (i - n) := by sorry
