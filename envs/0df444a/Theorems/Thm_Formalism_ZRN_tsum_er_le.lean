-- Prove2me | Theorems.Thm_Formalism_ZRN_tsum_er_le
-- name    : Formalism.ZRN.tsum_er_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:43:13.661578+00:00
-- url     : https://prove2.me/theorems/1825d696-3f99-4c92-a4f6-103af1423b10
-- title:
--   ZRN: tsum er le
-- statement:
--   The ZRN construction uses the tsum er le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L305-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L305-L317

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

theorem Formalism.ZRN.tsum_er_le (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) : ∑' n, er n σ ≤ 1 - σ := by sorry
