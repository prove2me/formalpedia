-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CSym_eF_of_genE_mul
-- name    : Formalism.InvariantFactorPaths.G7.CSym.eF_of_genE_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:02.073802+00:00
-- url     : https://prove2.me/theorems/6fc79b2f-9d51-4ea6-9bf4-e5c9ac3f7ff5
-- title:
--   CSym: e F of gen E mul
-- statement:
--   The CSym construction uses the e F of gen E mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/GaussElementarySymmetric.lean#L50-L54

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
variable {K σ : Type} [CommRing K] [Fintype σ]

theorem Formalism.InvariantFactorPaths.G7.CSym.eF_of_genE_mul {τ ρ : Type} [Fintype τ] [Fintype ρ] (z : σ → K) (x : τ → K) (y : ρ → K)
    (h : genE z = genE x * genE y) (n : ℕ) :
    eF z n = ∑ a ∈ range (n + 1), eF x a * eF y (n - a) := by sorry
