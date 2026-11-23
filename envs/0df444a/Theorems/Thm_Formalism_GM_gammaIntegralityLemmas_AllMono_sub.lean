-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sub
-- name    : Formalism.GM.gammaIntegralityLemmas.AllMono.sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:13.594472+00:00
-- url     : https://prove2.me/theorems/02bcae3b-7073-4e19-a3dd-2834f2166b59
-- title:
--   All Mono: sub
-- statement:
--   The All Mono construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L662-L664
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L662-L664

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

theorem Formalism.GM.gammaIntegralityLemmas.AllMono.sub {d : M} {P P' : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (h' : AllMono Q d P') :
    AllMono Q d (P - P') := by sorry
