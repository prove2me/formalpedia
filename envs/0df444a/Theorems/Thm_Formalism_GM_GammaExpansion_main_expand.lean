-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_main_expand
-- name    : Formalism.GM.GammaExpansion.main_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:37.714592+00:00
-- url     : https://prove2.me/theorems/1ec440f0-e6ce-4d89-a213-8a4acdada48e
-- title:
--   Gamma Expansion: main expand
-- statement:
--   The Gamma Expansion construction uses the main expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L643-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L643-L673

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

theorem Formalism.GM.GammaExpansion.main_expand (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r) (q : MvPolynomial σ k)
    (K : ℕ) (hq : ∀ s ∈ q.support, s (e ρ) ≤ K) (s j m : ℕ) :
    (Dp (e ρ) ^ m) ((tieE w e ^ s) ((tieF w e ^ j) (X (e ρ) ^ m * q))) =
      (m.factorial : k) • ∑ i ∈ range (s + 1), ∑ t ∈ range (K + 1),
        (((m.choose i * (m - i).choose t : ℕ) : k) * (s.descFactorial i : k) / ((i + t).factorial : k)) •
          (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s - i) *
            (tieF w e ^ j) (X (e ρ) ^ (i + t) * (Dp (e ρ) ^ t) q)) := by sorry
