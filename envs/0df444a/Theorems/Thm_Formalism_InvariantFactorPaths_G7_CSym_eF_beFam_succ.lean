-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_beFam_succ
-- name    : Formalism.InvariantFactorPaths.G7.CSym.eF_beFam_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:52.151535+00:00
-- url     : https://prove2.me/theorems/c4709ada-506f-4ad0-b89c-ad8a991b21fd
-- title:
--   CSym: e F be Fam succ
-- statement:
--   The CSym construction uses the e F be Fam succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L119-L124

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

theorem Formalism.InvariantFactorPaths.G7.CSym.eF_beFam_succ (Q : K) (hQ : Q ≠ 0) (g l : ℕ) :
    eF (beFam Q (g + 1)) (l + 1) =
      Q ^ (l + 1) * eF (beFam Q g) (l + 1) + Q ^ (-(g : ℤ)) * (Q ^ l * eF (beFam Q g) l) := by sorry
