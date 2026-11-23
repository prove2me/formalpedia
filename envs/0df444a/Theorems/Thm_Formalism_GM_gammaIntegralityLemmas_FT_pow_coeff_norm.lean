-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_pow_coeff_norm
-- name    : Formalism.GM.gammaIntegralityLemmas.FT_pow_coeff_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:47.890208+00:00
-- url     : https://prove2.me/theorems/5d9d6c6c-fa8d-478a-ab02-e702229ae7f2
-- title:
--   gamma Integrality Lemmas: FT pow coeff norm
-- statement:
--   The gamma Integrality Lemmas construction uses the FT pow coeff norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L548-L600
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L548-L600

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

theorem Formalism.GM.gammaIntegralityLemmas.FT_pow_coeff_norm (hwe : ∀ c, w c ≠ e c) (Tb B : ℕ) (hB : Nat.log p Tb ≤ B) (K : ℝ)
    (G : MvPolynomial σ ℚ_[p]) (hG : ∀ β, ‖coeff β G‖ ≤ K) (T : Finset (Fin r)) :
    ∀ b ≤ Tb, ∀ β, ‖coeff β ((FT w e T ^ b) G)‖ ≤
      K * (p : ℝ) ^ (((T.card * B : ℕ) : ℤ) - 2 * (padicValNat p b.factorial : ℤ)) := by sorry
