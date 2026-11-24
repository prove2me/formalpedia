-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_weight_rowWeights_eq_rowDeg
-- name    : Formalism.CohomologicalDescent.DepthNonnegative.weight_rowWeights_eq_rowDeg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:10:57.627652+00:00
-- url     : https://prove2.me/theorems/b68c5c75-15f7-4053-a0d6-28612ef4952c
-- title:
--   Depth Nonnegative: weight row Weights eq row Deg
-- statement:
--   The Depth Nonnegative construction uses the weight row Weights eq row Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L79-L87

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

theorem Formalism.CohomologicalDescent.DepthNonnegative.weight_rowWeights_eq_rowDeg {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = rowDeg m a := by sorry
