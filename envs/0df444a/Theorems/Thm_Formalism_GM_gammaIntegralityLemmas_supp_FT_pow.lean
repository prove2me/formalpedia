-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_supp_FT_pow
-- name    : Formalism.GM.gammaIntegralityLemmas.supp_FT_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:58.019898+00:00
-- url     : https://prove2.me/theorems/6d1d7683-d9c5-440c-8d9d-f16ae0c56330
-- title:
--   gamma Integrality Lemmas: supp FT pow
-- statement:
--   The gamma Integrality Lemmas construction uses the supp FT pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L527-L546
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L527-L546

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
variable {σ : Type} [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem Formalism.GM.gammaIntegralityLemmas.supp_FT_pow (T : Finset (Fin r)) (Q : ℕ → (σ →₀ ℕ) → Prop)
    (hstep : ∀ b β c, c ∈ T → Q b (β + Finsupp.single (w c) 1 + Finsupp.single (e c) 1) → Q (b + 1) β)
    (hwe : ∀ c, w c ≠ e c)
    (G : MvPolynomial σ ℚ_[p]) (h0 : ∀ β ∈ G.support, Q 0 β) :
    ∀ b, ∀ β ∈ ((FT w e T ^ b) G).support, Q b β := by sorry
