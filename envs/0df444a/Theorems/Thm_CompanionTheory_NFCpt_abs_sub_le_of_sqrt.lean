-- Prove2me | Theorems.Thm_CompanionTheory_NFCpt_abs_sub_le_of_sqrt
-- name    : CompanionTheory.NFCpt.abs_sub_le_of_sqrt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:19.048662+00:00
-- url     : https://prove2.me/theorems/7d75eeb9-4420-53f9-a6b9-9edd4a54a962
-- title:
--   NFCpt: abs sub le of sqrt
-- statement:
--   The NFCpt construction uses the abs sub le of sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/DiscreteGroupWaves/IntegralEqOfSqrtCauchy.lean#L82-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/DiscreteGroupWaves/IntegralEqOfSqrtCauchy.lean#L82-L99

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_DiscreteGroupWaves_IntegralEqOfSqrtCauchy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.NFCpt
open MeasureTheory Filter Topology

theorem CompanionTheory.NFCpt.abs_sub_le_of_sqrt {a b d δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hδ : 0 < δ)
    (h : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt d) : |a - b| ≤ d / δ + δ * (a + b) := by sorry
