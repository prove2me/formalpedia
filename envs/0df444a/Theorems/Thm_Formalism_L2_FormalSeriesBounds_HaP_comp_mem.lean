-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_comp_mem
-- name    : Formalism.L2.FormalSeriesBounds.HaP.comp_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:36.608826+00:00
-- url     : https://prove2.me/theorems/f979f716-df60-4b93-a838-b146e57867c9
-- title:
--   Ha P: comp mem
-- statement:
--   The Ha P construction uses the comp mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L106-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L106-L127

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {K : Type} [Field K] [CharZero K] {σ : Type}
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ) {cc : Ty → Ty} {isX : Ty → Prop} {a : Ty → ℕ → ℕ}

theorem Formalism.L2.FormalSeriesBounds.HaP.comp_mem (lam : K →ₗ[ℚ] ℚ) {P : MvPolynomial (Letter Ty r n) K} (hP : P ∈ HHa r n K cc isX a) :
    comp lam P ∈ HHa r n ℚ cc isX a := by sorry
