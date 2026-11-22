-- Prove2me | Theorems.Thm_Formalism_GM_TM_mem_intPol_of_norm
-- name    : Formalism.GM.TM.mem_intPol_of_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:00.741402+00:00
-- url     : https://prove2.me/theorems/ffd1f544-debe-44b5-8c49-4263c1e9bace
-- title:
--   TM: mem int Pol of norm
-- statement:
--   The TM construction uses the mem int Pol of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L86-L94

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.GM.TM.mem_intPol_of_norm {σ : Type} (x : MvPolynomial σ ℚ_[p]) (h : ∀ m, ‖x.coeff m‖ ≤ 1) :
    x ∈ IntPol p σ := by sorry
