-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_genE_FFam_succ
-- name    : Formalism.InvariantFactorPaths.G7.CSym.genE_FFam_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:54.838485+00:00
-- url     : https://prove2.me/theorems/3a5f6dbb-698b-4ccf-86f5-f2b8557c77af
-- title:
--   CSym: gen E FFam succ
-- statement:
--   The CSym construction uses the gen E FFam succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L193-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L193-L198

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
open Formalism.InvariantFactorPaths.G7.CSym

theorem Formalism.InvariantFactorPaths.G7.CSym.genE_FFam_succ {K : Type} [Field K] (Q : K) (t : ℕ) (m : ℕ → K) (j : ℕ) :
    genE (FFam Q t m (j + 1)) =
      genE (fun x => m (j + 1) * beFam Q (t + 1) x) * genE (FFam Q t m j) := by sorry
