-- Prove2me | Theorems.Thm_Formalism_ZRN_summable_e
-- name    : Formalism.ZRN.summable_e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:43:33.293023+00:00
-- url     : https://prove2.me/theorems/b621eba0-5b0e-4cb0-91cb-1a57ac4428eb
-- title:
--   ZRN: summable e
-- statement:
--   The ZRN construction uses the summable e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L191-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L191-L193

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

theorem Formalism.ZRN.summable_e (s : ℂ) (h : 0 < s.re) : Summable (fun n => e n s) := by sorry
