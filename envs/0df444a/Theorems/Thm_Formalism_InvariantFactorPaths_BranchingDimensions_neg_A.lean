-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_neg_A
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.neg_A
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:17.789749+00:00
-- url     : https://prove2.me/theorems/e69f97f0-7459-4ef2-bf69-29b9cc061846
-- title:
--   Branching Dimensions: neg A
-- statement:
--   The Branching Dimensions construction uses the neg A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L612-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L612-L622

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
variable {D : Letters} {mu : D.Stages}

theorem Formalism.InvariantFactorPaths.BranchingDimensions.neg_A (hP : D.IsPATH mu) (i u : ℕ) (ha : actC D (i + 1) = true) :
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) (u + 1) ≤ tailNeg (D.stLen i) (stage mu i) u ∧
      D.SNeg (u + 1) (i + 1) = D.SNeg u i := by sorry
