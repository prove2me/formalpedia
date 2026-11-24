-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_ent_sign
-- name    : Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.ent_sign
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:04.766268+00:00
-- url     : https://prove2.me/theorems/96d68f11-ab25-4509-bcfc-582d0aaa277d
-- title:
--   TTyp: ent sign
-- statement:
--   The TTyp construction uses the ent sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/AtypicalWeightBoundOf.lean#L42-L57

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

theorem Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.ent_sign (h20 : PathEntryBounds) {D : Letters} {mu : D.Stages} (hW : D.Wf) (hP : D.IsPATH mu)
    {i m : ℕ} (hi : i ≤ D.Ns) (hm : m < D.k) :
    (m + D.Ns < D.k → 0 ≤ ent mu i m) ∧ (D.Ns ≤ m → ent mu i m ≤ 0) := by sorry
