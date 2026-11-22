-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_prod
-- name    : Formalism.GM.gammaIntegralityLemmas.AllMono.prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:46.51782+00:00
-- url     : https://prove2.me/theorems/b74a38d1-e88e-4de4-9d40-da787817994e
-- title:
--   All Mono: prod
-- statement:
--   The All Mono construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L675-L683
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L675-L683

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

theorem Formalism.GM.gammaIntegralityLemmas.AllMono.prod (hQ : ∀ d d' β β', Q d β → Q d' β' → Q (d + d') (β + β')) (hQ0 : Q 0 0)
    {ι : Type} (s : Finset ι) (d : ι → M) (P : ι → MvPolynomial σ ℚ_[p])
    (h : ∀ i ∈ s, AllMono Q (d i) (P i)) : AllMono Q (∑ i ∈ s, d i) (∏ i ∈ s, P i) := by sorry
