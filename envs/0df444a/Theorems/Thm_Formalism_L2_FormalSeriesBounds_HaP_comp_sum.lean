-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_comp_sum
-- name    : Formalism.L2.FormalSeriesBounds.HaP.comp_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:42.629927+00:00
-- url     : https://prove2.me/theorems/56ef15b2-de10-459f-958a-57a4e16228c1
-- title:
--   Ha P: comp sum
-- statement:
--   The Ha P construction uses the comp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L74-L77

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

theorem Formalism.L2.FormalSeriesBounds.HaP.comp_sum (lam : K →ₗ[ℚ] ℚ) {α : Type} (s : Finset α) (f : α → MvPolynomial σ K) :
    comp lam (∑ i ∈ s, f i) = ∑ i ∈ s, comp lam (f i) := by sorry
