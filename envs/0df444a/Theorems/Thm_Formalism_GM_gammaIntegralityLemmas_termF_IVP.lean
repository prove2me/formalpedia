-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_termF_IVP
-- name    : Formalism.GM.gammaIntegralityLemmas.termF_IVP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:12.704977+00:00
-- url     : https://prove2.me/theorems/5180caab-9c2e-4e6a-9364-ed3288d413a5
-- title:
--   gamma Integrality Lemmas: term F IVP
-- statement:
--   The gamma Integrality Lemmas construction uses the term F IVP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1259-L1403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1259-L1403

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}

theorem Formalism.GM.gammaIntegralityLemmas.termF_IVP (LL : Letters (N + 1)) (ρ : Fin r) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (z j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (β γ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hβd : δv β + (j - a) • eWY = (LL.snoc LL.total).deg) (hβp : β (xW ρ) ≤ β (yE ρ))
    (hγd : δv γ + (j - a') • eWY = (LL.snoc LL.total).deg) (hγp : γ (xW ρ) ≤ γ (yE ρ))
    (h h' : ℚ_[p])
    (hh : ‖h‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))))
    (hh' : ‖h'‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ)))) :
    IVP p (LL.total + LL.deg (Fin.last N))
      (fun m => (p : ℚ_[p]) ^ (kap N r B) * termF LL ρ z j a a' β γ h h' m) := by sorry
