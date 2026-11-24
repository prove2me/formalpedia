-- Prove2me | Theorems.Thm_Formalism_GM_div_mem_zpS
-- name    : Formalism.GM.div_mem_zpS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:26.70548+00:00
-- url     : https://prove2.me/theorems/bba886be-83bb-4e9e-9aac-cdc3a9f05722
-- title:
--   GM: div mem zp S
-- statement:
--   The GM construction uses the div mem zp S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/Mahler.lean#L57-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/Mahler.lean#L57-L72

import Definitions.Def_Formalism_MahlerMeasure_StatementB
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_Mahler
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Polynomial

theorem Formalism.GM.div_mem_zpS (p k m : ℕ) [hp : Fact p.Prime] (hm1 : 1 ≤ m) (hm : m ≤ p ^ k) :
    ((p : ℚ) ^ k / m) ∈ zpS p := by sorry
