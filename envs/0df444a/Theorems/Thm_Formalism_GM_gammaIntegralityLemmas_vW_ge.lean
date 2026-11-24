-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vW_ge
-- name    : Formalism.GM.gammaIntegralityLemmas.vW_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:51.712497+00:00
-- url     : https://prove2.me/theorems/47d85f58-36c8-40b5-87c2-aa5f32177f62
-- title:
--   gamma Integrality Lemmas: v W ge
-- statement:
--   The gamma Integrality Lemmas construction uses the v W ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1035-L1047
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1035-L1047

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

theorem Formalism.GM.gammaIntegralityLemmas.vW_ge (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) {T B : ℕ} (hB : Nat.log p T ≤ B)
    (hT : ∀ i, δv δ i ≤ T) :
    ∑ i, padicValNat p (δv δ i).factorial ≤
      padicValNat p (∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) + (N + 2) * (r * B) := by sorry
