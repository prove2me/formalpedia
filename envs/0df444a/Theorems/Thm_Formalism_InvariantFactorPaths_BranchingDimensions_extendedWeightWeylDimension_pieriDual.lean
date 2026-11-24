-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_pieriDual
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.pieriDual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:57.362819+00:00
-- url     : https://prove2.me/theorems/1e6ec586-410e-4e97-8ee4-b7bc20959b01
-- title:
--   extended Weight Weyl Dimension: pieri Dual
-- statement:
--   The extended Weight Weyl Dimension construction uses the pieri Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L126-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/TTotal.lean#L126-L149

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
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
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension

theorem Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.pieriDual (hP : PieriDim) (n : ℕ) (mu : Fin n → ℤ) (B : ℕ) (hn : 1 ≤ n) (hd : Dom n (extW mu)) :
    ∑ᶠ (mu' : Fin n → ℤ) (_ : HStrip n (extW mu') (extW mu) ∧ wsize n (extW mu) - wsize n (extW mu') = B),
      weylDim n (extW mu') = weylDim n (extW mu) * ((B + n - 1).choose (n - 1) : ℝ) := by sorry
