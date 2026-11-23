-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_tieGam_expand
-- name    : Formalism.GM.gammaIntegralityLemmas.tieGam_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:00.430865+00:00
-- url     : https://prove2.me/theorems/3fa7cd15-fd48-4a35-b92a-6b14a49b9144
-- title:
--   gamma Integrality Lemmas: tie Gam expand
-- statement:
--   The gamma Integrality Lemmas construction uses the tie Gam expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1472-L1492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L1472-L1492

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

theorem Formalism.GM.gammaIntegralityLemmas.tieGam_expand (LL : Letters (N + 1)) (ρ : Fin r) (z : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (m : ℕ) :
    tieGam p LL ρ z (m + LL.total) f f' =
      ∑ j ∈ range (LL.deg (Fin.last N) + 1), ∑ a ∈ range (j + 1), ∑ a' ∈ range (j + 1),
        ∑ β ∈ ((FT wv ev (univ.erase ρ) ^ (j - a)) (aeval (freezeSub p LL ρ) f)).support,
          ∑ γ ∈ ((FT wv ev (univ.erase ρ) ^ (j - a')) (aeval (freezeSub p LL ρ) f')).support,
            termF LL ρ z j a a' β γ (coeff β ((FT wv ev (univ.erase ρ) ^ (j - a)) (aeval (freezeSub p LL ρ) f)))
              (coeff γ ((FT wv ev (univ.erase ρ) ^ (j - a')) (aeval (freezeSub p LL ρ) f'))) m := by sorry
