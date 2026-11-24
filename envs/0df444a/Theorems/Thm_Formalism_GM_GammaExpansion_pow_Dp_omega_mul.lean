-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_omega_mul
-- name    : Formalism.GM.GammaExpansion.pow_Dp_omega_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:33.587143+00:00
-- url     : https://prove2.me/theorems/95b6009e-cd71-4099-b595-6b91da1a31b8
-- title:
--   Gamma Expansion: pow Dp omega mul
-- statement:
--   The Gamma Expansion construction uses the pow Dp omega mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L584-L598
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L584-L598

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}

theorem Formalism.GM.GammaExpansion.pow_Dp_omega_mul (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r) (s m : ℕ)
    (V : MvPolynomial σ k) :
    (Dp (e ρ) ^ m) ((∑ c, X (w c) * X (e c)) ^ s * V) =
      ∑ i ∈ range (s + 1), (m.choose i * s.descFactorial i) •
        (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s - i) * (Dp (e ρ) ^ (m - i)) V) := by sorry
