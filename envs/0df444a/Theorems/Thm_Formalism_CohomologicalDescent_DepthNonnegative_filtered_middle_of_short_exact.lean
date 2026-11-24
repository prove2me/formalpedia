-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_filtered_middle_of_short_exact
-- name    : Formalism.CohomologicalDescent.DepthNonnegative.filtered_middle_of_short_exact
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:12.729273+00:00
-- url     : https://prove2.me/theorems/c9f561c4-83eb-4dd2-b1e5-f3ad728d86ea
-- title:
--   Depth Nonnegative: filtered middle of short exact
-- statement:
--   The Depth Nonnegative construction uses the filtered middle of short exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L431-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L431-L488

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
open CategoryTheory CategoryTheory.Limits

theorem Formalism.CohomologicalDescent.DepthNonnegative.filtered_middle_of_short_exact {C : Type 1} [Category.{0} C] [Abelian C] {P : C → Prop} {Z : C}
    (hZ : Filtered P Z) : ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact → Filtered P X → Filtered P Y := by sorry
