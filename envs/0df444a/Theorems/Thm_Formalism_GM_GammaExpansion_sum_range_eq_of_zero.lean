-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_sum_range_eq_of_zero
-- name    : Formalism.GM.GammaExpansion.sum_range_eq_of_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:35.511719+00:00
-- url     : https://prove2.me/theorems/d25f19d5-3d42-48b0-8f89-d99612aa072e
-- title:
--   Gamma Expansion: sum range eq of zero
-- statement:
--   The Gamma Expansion construction uses the sum range eq of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L556-L561
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L556-L561

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

theorem Formalism.GM.GammaExpansion.sum_range_eq_of_zero {M : Type} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ)
    (ha : ∀ i, a ≤ i → f i = 0) (hb : ∀ i, b ≤ i → f i = 0) :
    ∑ i ∈ range a, f i = ∑ i ∈ range b, f i := by sorry
