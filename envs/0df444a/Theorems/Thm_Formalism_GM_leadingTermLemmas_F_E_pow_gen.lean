-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_F_E_pow_gen
-- name    : Formalism.GM.leadingTermLemmas.F_E_pow_gen
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:35:49.840831+00:00
-- url     : https://prove2.me/theorems/44c4bdd6-25f5-4c79-9ace-6113ab68cb25
-- title:
--   leading Term Lemmas: F E pow gen
-- statement:
--   The leading Term Lemmas construction uses the F E pow gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L295-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L295-L308

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe

theorem Formalism.GM.leadingTermLemmas.F_E_pow_gen {a b : ℕ} {y : MvPolynomial σ K} (hy : BiHom w e a b y) (j : ℕ) :
    tieF w e ((tieE w e ^ (j + 1)) y) =
      (tieE w e ^ (j + 1)) (tieF w e y) + (((j + 1) * (a + b + r + j) : ℕ) : K) • (tieE w e ^ j) y := by sorry
