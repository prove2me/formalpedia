-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sum
-- name    : Formalism.GM.gammaIntegralityLemmas.AllMono.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:25.055802+00:00
-- url     : https://prove2.me/theorems/4e6a59a5-8c44-4d96-a69f-6a9a8376567f
-- title:
--   All Mono: sum
-- statement:
--   The All Mono construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L636-L643
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L636-L643

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

theorem Formalism.GM.gammaIntegralityLemmas.AllMono.sum {ι : Type} (s : Finset ι) {d : M} (P : ι → MvPolynomial σ ℚ_[p])
    (h : ∀ i ∈ s, AllMono Q d (P i)) : AllMono Q d (∑ i ∈ s, P i) := by sorry
