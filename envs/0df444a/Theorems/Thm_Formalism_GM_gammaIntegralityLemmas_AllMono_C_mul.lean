-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_C_mul
-- name    : Formalism.GM.gammaIntegralityLemmas.AllMono.C_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:45.028798+00:00
-- url     : https://prove2.me/theorems/484852ab-48a3-48e0-acf7-89e41d7f0366
-- title:
--   All Mono: C mul
-- statement:
--   The All Mono construction uses the C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L653-L657
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L653-L657

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

theorem Formalism.GM.gammaIntegralityLemmas.AllMono.C_mul (a : ℚ_[p]) {d : M} {P : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) :
    AllMono Q d (C a * P) := by sorry
