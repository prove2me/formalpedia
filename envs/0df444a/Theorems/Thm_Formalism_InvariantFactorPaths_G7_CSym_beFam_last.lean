-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_beFam_last
-- name    : Formalism.InvariantFactorPaths.G7.CSym.beFam_last
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:07.086802+00:00
-- url     : https://prove2.me/theorems/1b97801b-1c31-4739-b0f3-96753a30dffa
-- title:
--   CSym: be Fam last
-- statement:
--   The CSym construction uses the be Fam last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L113-L117

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
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.CSym.beFam_last (Q : K) (g : ℕ) : beFam Q (g + 1) (Fin.last g) = Q ^ (-(g : ℤ)) := by sorry
