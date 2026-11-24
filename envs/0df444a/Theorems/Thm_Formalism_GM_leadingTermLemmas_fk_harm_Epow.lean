-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_harm_Epow
-- name    : Formalism.GM.leadingTermLemmas.fk_harm_Epow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:00.044693+00:00
-- url     : https://prove2.me/theorems/b514527f-4cb5-4860-a8b7-e73a834075f1
-- title:
--   leading Term Lemmas: fk harm Epow
-- statement:
--   The leading Term Lemmas construction uses the fk harm Epow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L315-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L315-L317

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

theorem Formalism.GM.leadingTermLemmas.fk_harm_Epow {g : MvPolynomial σ K} (hF : tieF w e g = 0) {t : ℕ} (ht : 1 ≤ t)
    (u : MvPolynomial σ K) : fk g ((tieE w e ^ t) u) = 0 := by sorry
