-- Prove2me | Theorems.Thm_Formalism_GM_TM_mmwZ_fg
-- name    : Formalism.GM.TM.mmwZ_fg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:00.690823+00:00
-- url     : https://prove2.me/theorems/ac92b7de-b2a9-49be-b5f1-0f49aeca375f
-- title:
--   TM: mmw Z fg
-- statement:
--   The TM construction uses the mmw Z fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L545-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L545-L551

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
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.GM.TM.mmwZ_fg {K r : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (w : Fin r → ℤ) : (MMwZ p LLw J M ρ w).FG := by sorry
