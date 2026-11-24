-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_Fpow_harm
-- name    : Formalism.GM.leadingTermLemmas.Fpow_harm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:00.678064+00:00
-- url     : https://prove2.me/theorems/96a93ee4-a11e-471d-b6ce-90cab4651e5f
-- title:
--   leading Term Lemmas: Fpow harm
-- statement:
--   The leading Term Lemmas construction uses the Fpow harm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L310-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L310-L313

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

theorem Formalism.GM.leadingTermLemmas.Fpow_harm {u : MvPolynomial σ K} (hF : tieF w e u = 0) {t : ℕ} (ht : 1 ≤ t) :
    (tieF w e ^ t) u = 0 := by sorry
