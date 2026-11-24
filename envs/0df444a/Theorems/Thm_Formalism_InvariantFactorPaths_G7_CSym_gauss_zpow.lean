-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_gauss_zpow
-- name    : Formalism.InvariantFactorPaths.G7.CSym.gauss_zpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:37.086213+00:00
-- url     : https://prove2.me/theorems/095753b1-2643-4f0a-a4bb-d7c1a8977f10
-- title:
--   CSym: gauss zpow
-- statement:
--   The CSym construction uses the gauss zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L126-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L126-L153

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

theorem Formalism.InvariantFactorPaths.G7.CSym.gauss_zpow (Q : ℕ) (hQ : (Q : K) ≠ 0) : ∀ g l : ℕ,
    ((Formalism.G0.gaussBinom (Q ^ 2) g l : ℕ) : K) =
      (Q : K) ^ ((l : ℤ) * ((g : ℤ) - l)) * eF (beFam (Q : K) g) l
  := by sorry
