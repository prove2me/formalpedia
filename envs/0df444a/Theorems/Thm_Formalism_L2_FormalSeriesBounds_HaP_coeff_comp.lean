-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_coeff_comp
-- name    : Formalism.L2.FormalSeriesBounds.HaP.coeff_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:46:12.909231+00:00
-- url     : https://prove2.me/theorems/0912d7e0-c1a6-46b2-b7e8-9b121fc31f14
-- title:
--   Ha P: coeff comp
-- statement:
--   The Ha P construction uses the coeff comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L67-L69

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

theorem Formalism.L2.FormalSeriesBounds.HaP.coeff_comp (lam : K →ₗ[ℚ] ℚ) (P : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (comp lam P) = lam (coeff m P) := by sorry
