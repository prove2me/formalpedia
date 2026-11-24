-- Prove2me | Theorems.Thm_Formalism_ZRN_e_differentiable
-- name    : Formalism.ZRN.e_differentiable
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:42:32.454161+00:00
-- url     : https://prove2.me/theorems/68db7cff-bfd3-4487-a2b4-8cf702105a09
-- title:
--   ZRN: e differentiable
-- statement:
--   The ZRN construction uses the e differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L128-L133

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

theorem Formalism.ZRN.e_differentiable (n : ℕ) : Differentiable ℂ (e n) := by sorry
