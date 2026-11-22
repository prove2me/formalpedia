-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_key
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:07:48.118817+00:00
-- url     : https://prove2.me/theorems/07a4e247-23ca-4fa2-a7f3-a4d2c7ed68c6
-- title:
--   TTyp: key
-- statement:
--   The TTyp construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L313-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L313-L336

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.key (h31 : LogBinomialProperties) (h34 : LogBinomialDeficit) (k' K : ℕ) (la : ℕ → ℤ) (q : ℕ → Bool) (B : ℕ → ℕ) (n0 : ℕ)
    (hk : 1 ≤ k')
    (h1 : ∀ l, l < (lat q B n0).length → k' ≤ (lat q B n0).getD l 0)
    (h2 : ∀ l, l + 1 < (lat q B n0).length → 4 * (lat q B n0).getD (l + 1) 0 ≤ (lat q B n0).getD l 0)
    (h3 : ∀ u, tailPos K la u ≤ (((lat q B n0).drop u).sum : ℕ))
    (i₀ u : ℕ) (X : ℝ) (hX : 0 < X)
    (hd : ((tailPos K la (u + ((Icc (i₀ + 1) n0).filter (fun l => q l = true)).card) : ℤ) : ℝ) ≤
      ((((lat q B n0).drop (u + ((Icc (i₀ + 1) n0).filter (fun l => q l = true)).card)).sum : ℕ) : ℝ)
        - X) :
    u < (lat q B (min i₀ n0)).length ∧
    (∑ m ∈ range K, fT k' ((max (la m) 0 : ℤ) : ℝ)) -
      (∑ l ∈ range (lat q B n0).length, fT k' (((lat q B n0).getD l 0 : ℕ) : ℝ)) ≤
        -(X * k' / (4 * (((lat q B (min i₀ n0)).getD u 0 : ℕ) : ℝ))) := by sorry
