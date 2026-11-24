-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_phi_E_pow
-- name    : Formalism.GM.GammaExpansion.phi_E_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:38.624426+00:00
-- url     : https://prove2.me/theorems/f7bba0b5-65cc-4978-9ce3-80b9ba936db7
-- title:
--   Gamma Expansion: phi E pow
-- statement:
--   The Gamma Expansion construction uses the phi E pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L513-L546
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L513-L546

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

theorem Formalism.GM.GammaExpansion.phi_E_pow (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) :
    ∀ (s o n z : ℕ) (Z : MvPolynomial σ k), s ≤ o → s ≤ n →
      EW w Z = ((o - s : ℕ) : k) • Z → EW e Z = ((n - s : ℕ) : k) • Z →
      tiePhi w e o n z ((tieE w e ^ s) Z) =
        (∏ i ∈ range s, (((z : k) + 1 + i) / ((o + n + r + z - 1 - i : ℕ) : k))) •
          (tieE w e ^ s) (tiePhi w e (o - s) (n - s) (z + s) Z) := by sorry
