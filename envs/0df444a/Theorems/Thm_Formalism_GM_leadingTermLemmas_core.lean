-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_core
-- name    : Formalism.GM.leadingTermLemmas.core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:45.780795+00:00
-- url     : https://prove2.me/theorems/c60f96af-241b-4f87-b962-f29a34e0caac
-- title:
--   leading Term Lemmas: core
-- statement:
--   The leading Term Lemmas construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L535-L717
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L535-L717

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

theorem Formalism.GM.leadingTermLemmas.core (hr : 1 ≤ r) (o n z t : ℕ) (ht : t ≤ o) (hon : o < n)
    (v0 y v0' y' : MvPolynomial σ ℝ)
    (hv0 : BiHom w e (o - t) (n - t) v0) (hy : BiHom w e (o - t - 1) (n - t - 1) y)
    (hy0 : y ≠ 0 → 1 ≤ o - t ∧ 1 ≤ n - t)
    (hv0' : BiHom w e (o - t) (n - t) v0') (hy' : BiHom w e (o - t - 1) (n - t - 1) y')
    (hy0' : y' ≠ 0 → 1 ≤ o - t ∧ 1 ≤ n - t) :
    |fk (tiePhi w e o n z ((tieE w e ^ t) (v0 + tieE w e y))) ((tieE w e ^ t) (v0' + tieE w e y'))
        - kap0 o n z t r * fk v0 v0'| ≤
      (Kc o z * (fk (v0 + tieE w e y) (v0 + tieE w e y) + fk (v0' + tieE w e y') (v0' + tieE w e y')) +
        kap0 o n z t r * (fk (tieF w e v0) (tieF w e v0) + fk (tieF w e v0') (tieF w e v0'))) /
        (2 * ((n - o : ℕ) : ℝ)) := by sorry
