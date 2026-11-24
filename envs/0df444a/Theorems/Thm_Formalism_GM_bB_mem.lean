-- Prove2me | Theorems.Thm_Formalism_GM_bB_mem
-- name    : Formalism.GM.bB_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:46.593776+00:00
-- url     : https://prove2.me/theorems/a761ce62-992b-4ee6-9e07-f6adf3e136ad
-- title:
--   GM: b B mem
-- statement:
--   The GM construction uses the b B mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/Mahler.lean#L128-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/Mahler.lean#L128-L147

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

theorem Formalism.GM.bB_mem (p k : ℕ) [Fact p.Prime] : ∀ i, i ≤ p ^ k → ∀ t : ℤ, bB ((p : ℚ) ^ k) i t ∈ zpT p := by sorry
