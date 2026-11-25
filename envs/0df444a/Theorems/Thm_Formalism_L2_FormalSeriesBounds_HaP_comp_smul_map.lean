-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_comp_smul_map
-- name    : Formalism.L2.FormalSeriesBounds.HaP.comp_smul_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:48:09.742125+00:00
-- url     : https://prove2.me/theorems/59a263a2-437b-4b16-880a-3f4fd7ab2b8b
-- title:
--   Ha P: comp smul map
-- statement:
--   The Ha P construction uses the comp smul map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L79-L84

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

theorem Formalism.L2.FormalSeriesBounds.HaP.comp_smul_map (lam : K →ₗ[ℚ] ℚ) (c : K) (p : MvPolynomial σ ℚ) :
    comp lam (c • map (algebraMap ℚ K) p) = lam c • p := by sorry
