-- Prove2me | Theorems.Thm_Formalism_SA_P_place_bound
-- name    : Formalism.SA.P.place_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:24.841825+00:00
-- url     : https://prove2.me/theorems/1a94c4c7-8539-5d44-8db6-8bbf4a70f000
-- title:
--   P: place bound
-- statement:
--   The P construction uses the place bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/OneLeProdOfInt.lean#L13-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/OneLeProdOfInt.lean#L13-L52

import Definitions.Def_Formalism_LatticeRigidity_StatementD
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_OneLeProdOfInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField

theorem Formalism.SA.P.place_bound (a1 b1 c U U' O G α β : ℝ) (hc : 0 < c)
    (ha : c < a1 ^ 2) (hb : c < b1 ^ 2) (hU0 : 0 ≤ U) (hU'0 : 0 ≤ U')
    (hU : U ^ 2 = (b1 ^ 2 - c) / (a1 ^ 2 - c)) (hU' : U' ^ 2 = (b1 ^ 2 - c) / (a1 ^ 2 - c))
    (hO0 : 0 ≤ O) (hO : O ≤ a1 / (a1 ^ 2 - c) + U * U' * b1 / (b1 ^ 2 - c))
    (hG : 1 ≤ G) (hα : G * O = U' * α) (hβ : G * O = U * β) :
    α * β ≤ 4 * G ^ 2 * (a1 ^ 2 / (a1 ^ 2 - c)) * (b1 ^ 2 / (b1 ^ 2 - c)) / c := by sorry
