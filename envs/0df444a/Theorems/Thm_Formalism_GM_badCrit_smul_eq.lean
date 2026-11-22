-- Prove2me | Theorems.Thm_Formalism_GM_badCrit_smul_eq
-- name    : Formalism.GM.badCrit_smul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:04.609733+00:00
-- url     : https://prove2.me/theorems/5ba50167-0c0d-4d1b-b6fc-56bad3d35fb1
-- title:
--   GM: bad Crit smul eq
-- statement:
--   The GM construction uses the bad Crit smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L70-L71

import Definitions.Def_Formalism_MahlerMeasure_StatementT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Module
variable {p : ℕ} [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]

theorem Formalism.GM.badCrit_smul_eq (c : ℤ_[p]) (x : Vs) : c • x = (c : ℚ_[p]) • x := by sorry
