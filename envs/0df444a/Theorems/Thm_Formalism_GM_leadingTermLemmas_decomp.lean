-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_decomp
-- name    : Formalism.GM.leadingTermLemmas.decomp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:33.968472+00:00
-- url     : https://prove2.me/theorems/8500951f-7b29-4c98-9e94-609acc6a4132
-- title:
--   leading Term Lemmas: decomp
-- statement:
--   The leading Term Lemmas construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L354-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L354-L431

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

theorem Formalism.GM.leadingTermLemmas.decomp (hr : 1 ≤ r) : ∀ (a b : ℕ) (y : MvPolynomial σ K), BiHom w e a b y →
    ∃ u : ℕ → MvPolynomial σ K, y = ∑ l ∈ range (a + 1), (tieE w e ^ l) (u l) ∧
      ∀ l ∈ range (a + 1), tieF w e (u l) = 0 ∧ BiHom w e (a - l) (b - l) (u l) ∧ (u l ≠ 0 → l ≤ b) := by sorry
