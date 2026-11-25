-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Hunt_redAs_coe
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt.redAs_coe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:18.637344+00:00
-- url     : https://prove2.me/theorems/5d3545d3-3da7-4c90-b489-ae440632db98
-- title:
--   Hunt: red As coe
-- statement:
--   The Hunt construction uses the red As coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/IsIntegralOfAll.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/IsIntegralOfAll.lean#L16-L16

import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_IsIntegralOfAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
variable (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt.redAs_coe (m : Ideal A) (a : ↥(As O A)) : (redAs O A m a : A ⧸ m) = Ideal.Quotient.mk m a := by sorry
