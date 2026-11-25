-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_comp_comm
-- name    : Formalism.L2.FormalSeriesBounds.HaP.comp_comm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:38.321417+00:00
-- url     : https://prove2.me/theorems/d32151d3-a0ec-464a-9f42-79af729335ec
-- title:
--   Ha P: comp comm
-- statement:
--   The Ha P construction uses the comp comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L86-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L86-L102

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

theorem Formalism.L2.FormalSeriesBounds.HaP.comp_comm (lam : K →ₗ[ℚ] ℚ) (Φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (Ψ : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ)
    (h : ∀ m, Φ (monomial m 1) = map (algebraMap ℚ K) (Ψ (monomial m 1))) (P : MvPolynomial σ K) :
    comp lam (Φ P) = Ψ (comp lam P) := by sorry
