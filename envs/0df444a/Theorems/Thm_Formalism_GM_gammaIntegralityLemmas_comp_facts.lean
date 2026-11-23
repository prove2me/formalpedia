-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_comp_facts
-- name    : Formalism.GM.gammaIntegralityLemmas.comp_facts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:56.731006+00:00
-- url     : https://prove2.me/theorems/f10d2cca-8ee4-417e-90a3-467c3764aee6
-- title:
--   gamma Integrality Lemmas: comp facts
-- statement:
--   The gamma Integrality Lemmas construction uses the comp facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1096-L1116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1096-L1116

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}

theorem Formalism.GM.gammaIntegralityLemmas.comp_facts (LL : Letters (N + 1)) (b : ℕ) (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) (c0 c1 : ℕ)
    (hd : δv δ + Pi.single (Fin.castSucc (Fin.last N)) c0 + Pi.single (Fin.last (N + 1)) c1 + b • eWY =
      (LL.snoc LL.total).deg) :
    (∀ k : Fin N, δv δ (Fin.castSucc (Fin.castSucc k)) = LL.deg (Fin.castSucc k)) ∧
    δv δ (Fin.castSucc (Fin.last N)) + c0 + b = LL.deg (Fin.last N) ∧
    δv δ (Fin.last (N + 1)) + c1 + b = LL.total := by sorry
