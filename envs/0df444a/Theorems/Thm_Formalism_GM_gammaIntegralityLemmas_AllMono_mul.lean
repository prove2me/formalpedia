-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
-- name    : Formalism.GM.gammaIntegralityLemmas.AllMono.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:27.843833+00:00
-- url     : https://prove2.me/theorems/be7800c9-a280-4845-9c18-f1e1d5d4f237
-- title:
--   All Mono: mul
-- statement:
--   The All Mono construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L620-L624
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L620-L624

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

theorem Formalism.GM.gammaIntegralityLemmas.AllMono.mul (hQ : ∀ d d' β β', Q d β → Q d' β' → Q (d + d') (β + β')) {d d' : M}
    {P P' : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (h' : AllMono Q d' P') : AllMono Q (d + d') (P * P') := by sorry
