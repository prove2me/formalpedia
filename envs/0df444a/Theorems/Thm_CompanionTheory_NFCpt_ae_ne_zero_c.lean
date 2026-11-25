-- Prove2me | Theorems.Thm_CompanionTheory_NFCpt_ae_ne_zero_c
-- name    : CompanionTheory.NFCpt.ae_ne_zero_c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:33.940846+00:00
-- url     : https://prove2.me/theorems/0bb9b242-f3f0-4169-bba7-64e3cd07444b
-- title:
--   NFCpt: ae ne zero c
-- statement:
--   The NFCpt construction uses the ae ne zero c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/DiscreteGroupWaves/IntegralEqOfSqrtCauchy.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/DiscreteGroupWaves/IntegralEqOfSqrtCauchy.lean#L14-L16

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

theorem CompanionTheory.NFCpt.ae_ne_zero_c : ∀ᵐ t : ℂ, t ≠ 0 := by sorry
