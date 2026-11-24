-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_linkage_depth_eq_sum_difference
-- name    : Formalism.CohomologicalDescent.ShortWeightBounds.linkage_depth_eq_sum_difference
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:43.123605+00:00
-- url     : https://prove2.me/theorems/deeb2c25-39da-425e-9f47-b12609508368
-- title:
--   Short Weight Bounds: linkage depth eq sum difference
-- statement:
--   The Short Weight Bounds construction uses the linkage depth eq sum difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L512-L522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L512-L522

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds

theorem Formalism.CohomologicalDescent.ShortWeightBounds.linkage_depth_eq_sum_difference (N k j t q : ℕ) (hN : k + j + t + q = N) (lam : ℕ → ℕ) (w : Fin N → ℕ)
    (U U' : Fin (k + j + t + q) → ℤ) (hU : ∀ a, U a = UN N lam a)
    (hU' : ∀ (a : Fin (k + j + t + q)) (a' : Fin N), (a : ℕ) = (a' : ℕ) →
      U' a = (w a' : ℤ) + (N : ℤ) - 1 - ((a : ℕ) : ℤ)) :
    depth2 (res N (varpi (k + j))) (res N lam) w =
      ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U a - U' a) := by sorry
