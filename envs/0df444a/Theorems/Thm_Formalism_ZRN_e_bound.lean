-- Prove2me | Theorems.Thm_Formalism_ZRN_e_bound
-- name    : Formalism.ZRN.e_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:41:40.85277+00:00
-- url     : https://prove2.me/theorems/5e7b45ec-8ed9-4cdd-8c46-f02eca21c719
-- title:
--   ZRN: e bound
-- statement:
--   The ZRN construction uses the e bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L16-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L16-L92

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

theorem Formalism.ZRN.e_bound (n : ℕ) (s : ℂ) (hs : ‖1 - s‖ ≤ (n : ℝ) + 1) :
    ‖e n s‖ ≤ (‖1 - s‖ ^ 2 + ‖1 - s‖) * ((n : ℝ) + 1) ^ (-1 - s.re) := by sorry
