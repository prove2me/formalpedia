-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_finite_quotient_of_pow_smul_mem
-- name    : Formalism.CohomologicalDescent.DepthNonnegative.finite_quotient_of_pow_smul_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:09:55.844556+00:00
-- url     : https://prove2.me/theorems/56713180-9613-4120-a1bf-47af47d3bccc
-- title:
--   Depth Nonnegative: finite quotient of pow smul mem
-- statement:
--   The Depth Nonnegative construction uses the finite quotient of pow smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L804-L818
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L804-L818

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

theorem Formalism.CohomologicalDescent.DepthNonnegative.finite_quotient_of_pow_smul_mem (O : Type) [CommRing O] [IsNoetherianRing O] (V : Type) [AddCommGroup V]
    [Module O V] [Module.Finite O V] (l : O) (J : ℕ) (U : Submodule O V)
    (hfin : Finite (O ⧸ Ideal.span {l})) (hU : ∀ x : V, l ^ J • x ∈ U) : Finite (V ⧸ U) := by sorry
