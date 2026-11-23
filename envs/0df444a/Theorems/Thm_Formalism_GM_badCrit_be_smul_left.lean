-- Prove2me | Theorems.Thm_Formalism_GM_badCrit_be_smul_left
-- name    : Formalism.GM.badCrit_be_smul_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:55.227697+00:00
-- url     : https://prove2.me/theorems/0dcea5e0-a3d6-4816-844f-9a20e5710144
-- title:
--   GM: bad Crit be smul left
-- statement:
--   The GM construction uses the bad Crit be smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/BadCrit.lean#L73-L75

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

theorem Formalism.GM.badCrit_be_smul_left (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (c : ℤ_[p]) (x y : Vs) :
    be (c • x) y = (c : ℚ_[p]) * be x y := by sorry
