-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_decompE
-- name    : Formalism.GM.leadingTermLemmas.decompE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:43.160804+00:00
-- url     : https://prove2.me/theorems/eca112aa-8907-4331-b962-bd8b8c1d314a
-- title:
--   leading Term Lemmas: decomp E
-- statement:
--   The leading Term Lemmas construction uses the decomp E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L520-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L520-L533

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
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe

theorem Formalism.GM.leadingTermLemmas.decompE {K : Type} [Field K] [CharZero K] (hr : 1 ≤ r) (A B : ℕ) (y : MvPolynomial σ K)
    (hy : BiHom w e (A - 1) (B - 1) y) (hy0 : y ≠ 0 → 1 ≤ A ∧ 1 ≤ B) :
    ∃ yl : ℕ → MvPolynomial σ K, tieE w e y = ∑ l ∈ range A, (tieE w e ^ (l + 1)) (yl l) ∧
      ∀ l ∈ range A, tieF w e (yl l) = 0 ∧ BiHom w e (A - 1 - l) (B - 1 - l) (yl l) := by sorry
