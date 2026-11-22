-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_one
-- name    : Formalism.GM.gammaIntegralityLemmas.AllMono.one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:47.472662+00:00
-- url     : https://prove2.me/theorems/4bcf5d17-31e8-4eb8-8031-f0a44e993f2c
-- title:
--   All Mono: one
-- statement:
--   The All Mono construction uses the one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L645-L651
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L645-L651

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

theorem Formalism.GM.gammaIntegralityLemmas.AllMono.one (hQ0 : Q 0 0) : AllMono Q 0 (1 : MvPolynomial σ ℚ_[p]) := by sorry
