-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_pow
-- name    : Formalism.GM.gammaIntegralityLemmas.AllMono.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:19.131546+00:00
-- url     : https://prove2.me/theorems/9536ce2c-89f1-46c9-b307-15156d5cc004
-- title:
--   All Mono: pow
-- statement:
--   The All Mono construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L669-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L669-L673

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
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ] {M : Type} [AddCommMonoid M]
variable (Q : M → (σ →₀ ℕ) → Prop)

theorem Formalism.GM.gammaIntegralityLemmas.AllMono.pow (hQ : ∀ d d' β β', Q d β → Q d' β' → Q (d + d') (β + β')) (hQ0 : Q 0 0) {d : M}
    {P : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (n : ℕ) : AllMono Q (n • d) (P ^ n) := by sorry
