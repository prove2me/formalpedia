-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_X_mul_X
-- name    : Formalism.GM.gammaIntegralityLemmas.AllMono.X_mul_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:34.438914+00:00
-- url     : https://prove2.me/theorems/93b49a21-db55-4d76-9a35-2767a68f130d
-- title:
--   All Mono: X mul X
-- statement:
--   The All Mono construction uses the X mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L685-L691
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L685-L691

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

theorem Formalism.GM.gammaIntegralityLemmas.AllMono.X_mul_X (u u' : σ) (d : M) (hq : Q d (Finsupp.single u 1 + Finsupp.single u' 1)) :
    AllMono Q d (X u * X u' : MvPolynomial σ ℚ_[p]) := by sorry
