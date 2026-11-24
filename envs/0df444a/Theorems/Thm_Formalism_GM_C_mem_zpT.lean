-- Prove2me | Theorems.Thm_Formalism_GM_C_mem_zpT
-- name    : Formalism.GM.C_mem_zpT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:21.393799+00:00
-- url     : https://prove2.me/theorems/e61bd516-83bb-4e79-a7dd-86a119b19112
-- title:
--   GM: C mem zp T
-- statement:
--   The GM construction uses the C mem zp T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/Mahler.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/Mahler.lean#L43-L48

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

theorem Formalism.GM.C_mem_zpT (p : ℕ) [Fact p.Prime] {a : ℚ} (ha : a ∈ zpS p) : C a ∈ zpT p := by sorry
