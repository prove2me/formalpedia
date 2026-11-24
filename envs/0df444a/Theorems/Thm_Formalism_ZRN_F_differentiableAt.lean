-- Prove2me | Theorems.Thm_Formalism_ZRN_F_differentiableAt
-- name    : Formalism.ZRN.F_differentiableAt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:41:26.963095+00:00
-- url     : https://prove2.me/theorems/9f307461-2313-45b3-abdc-d37ac9f01db7
-- title:
--   ZRN: F differentiable At
-- statement:
--   The ZRN construction uses the F differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L184-L189

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN

theorem Formalism.ZRN.F_differentiableAt (s₀ : ℂ) (h : 0 < s₀.re) : DifferentiableAt ℂ F s₀ := by sorry
