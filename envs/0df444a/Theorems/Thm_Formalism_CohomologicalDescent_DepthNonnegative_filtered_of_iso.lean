-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_filtered_of_iso
-- name    : Formalism.CohomologicalDescent.DepthNonnegative.filtered_of_iso
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:22.938528+00:00
-- url     : https://prove2.me/theorems/6a940dc7-2d33-4450-a145-852c2ba9cb52
-- title:
--   Depth Nonnegative: filtered of iso
-- statement:
--   The Depth Nonnegative construction uses the filtered of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L419-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L419-L429

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

theorem Formalism.CohomologicalDescent.DepthNonnegative.filtered_of_iso {C : Type 1} [Category.{0} C] [Abelian C] {P : C → Prop} {Y : C}
    (h : Filtered P Y) : ∀ {Y' : C} (_ : Y ≅ Y'), Filtered P Y' := by sorry
