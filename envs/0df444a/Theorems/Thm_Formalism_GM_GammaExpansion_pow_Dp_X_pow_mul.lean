-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_pow_Dp_X_pow_mul
-- name    : Formalism.GM.GammaExpansion.pow_Dp_X_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:35.425412+00:00
-- url     : https://prove2.me/theorems/1bf56bc3-6416-4187-8658-a3027a7ccf6c
-- title:
--   Gamma Expansion: pow Dp X pow mul
-- statement:
--   The Gamma Expansion construction uses the pow Dp X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L600-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L600-L617

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

theorem Formalism.GM.GammaExpansion.pow_Dp_X_pow_mul (v : σ) (q : MvPolynomial σ k) (K M m : ℕ) (hq : ∀ s ∈ q.support, s v ≤ K) :
    (Dp v ^ M) (q * X v ^ m) =
      ∑ i ∈ range (K + 1), (M.choose i * m.descFactorial (M - i)) • ((Dp v ^ i) q * X v ^ (m - (M - i))) := by sorry
