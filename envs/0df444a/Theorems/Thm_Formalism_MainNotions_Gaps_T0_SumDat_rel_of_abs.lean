-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_rel_of_abs
-- name    : Formalism.MainNotions.Gaps.T0.SumDat.rel_of_abs
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:10.375735+00:00
-- url     : https://prove2.me/theorems/105f7034-ad3e-4f3b-9f6b-0f30bc70ae39
-- title:
--   Sum Dat: rel of abs
-- statement:
--   The Sum Dat construction uses the rel of abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L484-L515
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L484-L515

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0

theorem Formalism.MainNotions.Gaps.T0.SumDat.rel_of_abs {ι : Type*} (X : SumDat ι) {CP Z PP : ℝ} (hCP : 1 ≤ CP) (hZ : 2 ≤ Z)
    (hPP : PP = CP * Z ^ 12) (hD : 1 ≤ X.D) (h1 : X.P1 ≤ CP * Z ^ 6) (h2 : X.P2 ≤ CP * Z ^ 5)
    (h3 : X.P3 ≤ CP * Z ^ 3) (h4 : X.P4 ≤ 2 * (CP * Z ^ 10) * (CP * Z ^ 4)) : X.Rel PP := by sorry
