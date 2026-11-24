-- Prove2me | Theorems.Thm_Formalism_ZRN_er_nonneg
-- name    : Formalism.ZRN.er_nonneg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:43:19.918901+00:00
-- url     : https://prove2.me/theorems/f0102fb1-02eb-4d11-805c-435f16c4e77d
-- title:
--   ZRN: er nonneg
-- statement:
--   The ZRN construction uses the er nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L271-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L271-L285

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

theorem Formalism.ZRN.er_nonneg (n : ℕ) (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) : 0 ≤ er n σ := by sorry
