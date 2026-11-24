-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_absorb
-- name    : Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.absorb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:40:37.616306+00:00
-- url     : https://prove2.me/theorems/a839b2ca-765d-4184-8682-e5eda29fd3e9
-- title:
--   Num: absorb
-- statement:
--   The Num construction uses the absorb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L247-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean#L247-L260

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

theorem Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.absorb {k b c : ℝ} (hk : 1 ≤ k) (hb : 10 ^ 100 ≤ b) (hc0 : 0 ≤ c) (hc : c ≤ 10 ^ 100) {i j : ℕ} (hi : i ≤ 8)
    (hj : j + 1 ≤ 8) : c * k ^ i * b ^ j ≤ (k * b) ^ 8 := by sorry
