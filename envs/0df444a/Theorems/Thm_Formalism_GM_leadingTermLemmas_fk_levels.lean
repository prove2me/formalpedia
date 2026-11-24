-- Prove2me | Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_levels
-- name    : Formalism.GM.leadingTermLemmas.fk_levels
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:53.557803+00:00
-- url     : https://prove2.me/theorems/14dc07b4-3c53-4dab-b0ea-a0aacf690fe9
-- title:
--   leading Term Lemmas: fk levels
-- statement:
--   The leading Term Lemmas construction uses the fk levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L334-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean#L334-L352

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

theorem Formalism.GM.leadingTermLemmas.fk_levels (hr : 1 ≤ r) (s : ℕ) (R : Finset ℕ) (u u' : ℕ → MvPolynomial σ K) (c d : ℕ → K)
    (α β α' β' : ℕ → ℕ) (hu : ∀ l ∈ R, BiHom w e (α l) (β l) (u l) ∧ tieF w e (u l) = 0)
    (hu' : ∀ l ∈ R, BiHom w e (α' l) (β' l) (u' l) ∧ tieF w e (u' l) = 0) :
    fk (∑ l ∈ R, c l • (tieE w e ^ (s + l)) (u l)) (∑ l ∈ R, d l • (tieE w e ^ (s + l)) (u' l)) =
      ∑ l ∈ R, c l * d l * (((s + l).descFactorial (s + l) *
        (α' l + β' l + r - 1 + (s + l)).descFactorial (s + l) : ℕ) : K) * fk (u l) (u' l) := by sorry
