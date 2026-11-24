-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_iterated_fderiv_swap_first_two
-- name    : Formalism.IndefR.Eqv.iterated_fderiv_swap_first_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:17.492734+00:00
-- url     : https://prove2.me/theorems/0ac378f3-53c7-4f05-bf67-bf127d97e492
-- title:
--   Eqv: iterated fderiv swap first two
-- statement:
--   The Eqv construction uses the iterated fderiv swap first two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L24-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L24-L47

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.IndefR.Eqv.iterated_fderiv_swap_first_two {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {g : E → H} (hg : ContDiff ℝ ∞ g) (m : ℕ)
    (x : E) (v : Fin (m + 2) → E) :
    iteratedFDeriv ℝ (m + 2) g x (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ (m + 2) g x v := by sorry
