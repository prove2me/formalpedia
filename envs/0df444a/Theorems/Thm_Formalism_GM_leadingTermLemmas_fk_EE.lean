-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_EE
-- name    : Formalism.GM.leadingTermLemmas.fk_EE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:55.096836+00:00
-- url     : https://prove2.me/theorems/32020d1c-2c42-4af3-98cb-948256058bd5
-- title:
--   leading Term Lemmas: fk EE
-- statement:
--   The leading Term Lemmas construction uses the fk EE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L319-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L319-L332

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

theorem Formalism.GM.leadingTermLemmas.fk_EE (hr : 1 ≤ r) {a b a' b' : ℕ} {u u' : MvPolynomial σ K} (hu : BiHom w e a b u)
    (hF : tieF w e u = 0) (hu' : BiHom w e a' b' u') (hF' : tieF w e u' = 0) (i j : ℕ) :
    fk ((tieE w e ^ i) u) ((tieE w e ^ j) u') =
      if i = j then ((j.descFactorial j * (a' + b' + r - 1 + j).descFactorial j : ℕ) : K) * fk u u'
      else 0 := by sorry
