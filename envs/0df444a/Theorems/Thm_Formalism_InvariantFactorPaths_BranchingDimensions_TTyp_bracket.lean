-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_bracket
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.bracket
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:04.162798+00:00
-- url     : https://prove2.me/theorems/1a1b17e3-aee7-4308-b928-6f2bd0cd09d8
-- title:
--   TTyp: bracket
-- statement:
--   The TTyp construction uses the bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L160-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L160-L285

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
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
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.bracket (h31 : LogBinomialProperties) (h34 : LogBinomialDeficit) (k' K : ℕ) (la : ℕ → ℤ) (lst : List ℕ) (hk : 1 ≤ k')
    (h1 : ∀ l, l < lst.length → k' ≤ lst.getD l 0)
    (h2 : ∀ l, l + 1 < lst.length → 4 * lst.getD (l + 1) 0 ≤ lst.getD l 0)
    (h3 : ∀ u, tailPos K la u ≤ ((lst.drop u).sum : ℕ)) :
    (∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ)) -
      (∑ l ∈ range lst.length, fT k' ((lst.getD l 0 : ℕ) : ℝ)) ≤ 0 ∧
    ∀ (u₀ : ℕ) (X : ℝ), 0 < X → ((tailPos K la u₀ : ℤ) : ℝ) ≤ (((lst.drop u₀).sum : ℕ) : ℝ) - X →
      u₀ < lst.length ∧
      (∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ)) -
        (∑ l ∈ range lst.length, fT k' ((lst.getD l 0 : ℕ) : ℝ)) ≤
          -(X * k' / (4 * ((lst.getD u₀ 0 : ℕ) : ℝ))) := by sorry
