-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_choose_sub_expand
-- name    : Formalism.GM.gammaIntegralityLemmas.choose_sub_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:52.456967+00:00
-- url     : https://prove2.me/theorems/d874c823-2bde-4771-a4b1-b2070368ba0d
-- title:
--   gamma Integrality Lemmas: choose sub expand
-- statement:
--   The gamma Integrality Lemmas construction uses the choose sub expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L133-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L133-L166

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
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.GM.gammaIntegralityLemmas.choose_sub_expand (D : ℕ) : ∀ S k : ℕ, k ≤ D → ∃ e : ℕ → ℤ, ∀ n : ℕ, S ≤ n →
    (((n - S).choose k : ℕ) : ℤ) = ∑ i ∈ range (D + 1), e i * ((n.choose i : ℕ) : ℤ) := by sorry
