-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tails_range
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.tails_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:37.218337+00:00
-- url     : https://prove2.me/theorems/ea0a7f02-3c85-42a7-9adc-8e52cebf527a
-- title:
--   Branching Dimensions: tails range
-- statement:
--   The Branching Dimensions construction uses the tails range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L341-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/N0LeNs.lean#L341-L357

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.tails_range (hD : Dom D.k (ent mu D.n0))
    (hI : ∀ j, j < D.r → Interl (D.k - (j + 1)) (stage mu (D.n0 + (j + 1))) (stage mu (D.n0 + j))) :
    ∀ j, j ≤ D.r → ∀ l, l < D.k - j →
      ent mu D.n0 (D.k - 1) ≤ stage mu (D.n0 + j) l ∧ stage mu (D.n0 + j) l ≤ ent mu D.n0 0 := by sorry
