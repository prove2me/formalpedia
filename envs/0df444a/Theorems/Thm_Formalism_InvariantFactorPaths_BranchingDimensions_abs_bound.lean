-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_abs_bound
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.abs_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:38.201157+00:00
-- url     : https://prove2.me/theorems/9f5264fe-190a-4e0f-a981-79d5cfd98b61
-- title:
--   Branching Dimensions: abs bound
-- statement:
--   The Branching Dimensions construction uses the abs bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L157-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L157-L184

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters

theorem Formalism.InvariantFactorPaths.BranchingDimensions.abs_bound (N : ℕ) (T : ℕ → ℕ → ℤ) (S : ℕ → ℕ → ℕ) (act : ℕ → Bool)
    (h0 : ∀ u, T 0 u ≤ S u 0)
    (hA : ∀ i u, i < N → act (i + 1) = true → T (i + 1) (u + 1) ≤ T i u ∧ S (u + 1) (i + 1) = S u i)
    (hA0 : ∀ i, i < N → act (i + 1) = true → T (i + 1) 0 - T i 0 ≤ (S 0 (i + 1) : ℤ) - S 0 i)
    (hI : ∀ i u, i < N → act (i + 1) = false → T (i + 1) u ≤ T i u ∧ S u (i + 1) = S u i) :
    ∀ i, i ≤ N → ∀ u, T i u ≤ S u i := by sorry
