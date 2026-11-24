-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Hunt_isIntegral_of_all
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt.isIntegral_of_all
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:55:38.815183+00:00
-- url     : https://prove2.me/theorems/f53cb323-0375-4996-a091-6afad5e05491
-- title:
--   Hunt: is Integral of all
-- statement:
--   The Hunt construction uses the is Integral of all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/IsIntegralOfAll.lean#L20-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/IsIntegralOfAll.lean#L20-L56

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

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt.isIntegral_of_all (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [IsArtinianRing A] [IsReduced A] (a : A)
    (h : ∀ m : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk m.asIdeal a)) : IsIntegral O a := by sorry
