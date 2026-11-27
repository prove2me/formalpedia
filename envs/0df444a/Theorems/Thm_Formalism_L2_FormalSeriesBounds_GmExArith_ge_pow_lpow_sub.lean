-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_ge_pow_lpow_sub
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.ge_pow_lpow_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:18:06.363387+00:00
-- url     : https://prove2.me/theorems/0ab3b48f-ec61-45b0-9828-783675898c63
-- title:
--   Gm Ex Arith: ge pow lpow sub
-- statement:
--   The Gm Ex Arith construction uses the ge pow lpow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L181-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L181-L193

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}

theorem Formalism.L2.FormalSeriesBounds.GmExArith.ge_pow_lpow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) {w ε : ℝ} (h : V.Ge w (A - B))
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hεw : ε ≤ w) (k : ℕ) :
    V.Ge (w + k * ε) (A ^ (V.l ^ k) - B ^ (V.l ^ k)) := by sorry
