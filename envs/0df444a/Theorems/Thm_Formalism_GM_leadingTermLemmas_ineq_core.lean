-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_ineq_core
-- name    : Formalism.GM.leadingTermLemmas.ineq_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:34.005814+00:00
-- url     : https://prove2.me/theorems/c5f1b587-c52e-4eb4-a23d-8d77a186e3ea
-- title:
--   leading Term Lemmas: ineq core
-- statement:
--   The leading Term Lemmas construction uses the ineq core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L441-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L441-L496

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
open Finset

theorem Formalism.GM.leadingTermLemmas.ineq_core (A : ℕ) (δ Kc p0 : ℝ) (hδ : 0 < δ) (hKc : 0 ≤ Kc) (hp0 : 0 ≤ p0)
    (p nfv κ X X' Xc U U' Uc : ℕ → ℝ)
    (hX : ∀ l, 0 ≤ X l) (hX' : ∀ l, 0 ≤ X' l) (hU : ∀ l, 0 ≤ U l) (hU' : ∀ l, 0 ≤ U' l)
    (hXc : ∀ l, 2 * |Xc l| ≤ X l + X' l) (hUc : ∀ l, 2 * |Uc l| ≤ U l + U' l)
    (h0 : Uc 0 = Xc 0) (hnfv0 : nfv 0 = 1) (hpz : p 0 = p0) (hκ0 : κ 0 = 0)
    (hp : ∀ l, 1 ≤ l → l ≤ A → 0 ≤ p l ∧ p l * δ ≤ Kc * nfv l)
    (hnfv : ∀ l, 1 ≤ l → l ≤ A → 0 ≤ nfv l ∧ nfv l * δ ≤ κ l * nfv l) :
    |∑ l ∈ range (A + 1), p l * Uc l - p0 * ∑ l ∈ range (A + 1), nfv l * Xc l| ≤
      (Kc * ∑ l ∈ range (A + 1), nfv l * (U l + U' l) +
        p0 * ∑ l ∈ range (A + 1), κ l * nfv l * (X l + X' l)) / (2 * δ) := by sorry
