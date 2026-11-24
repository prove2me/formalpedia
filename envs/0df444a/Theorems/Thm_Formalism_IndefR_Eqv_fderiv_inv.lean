-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_fderiv_inv
-- name    : Formalism.IndefR.Eqv.fderiv_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:11.962356+00:00
-- url     : https://prove2.me/theorems/d6e18ff9-afd5-4dc7-88c3-38e6d0bd7edd
-- title:
--   Eqv: fderiv inv
-- statement:
--   The Eqv construction uses the fderiv inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L49-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L49-L65

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

theorem Formalism.IndefR.Eqv.fderiv_inv {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
    {Φ : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) H} (hΦ : Differentiable ℝ Φ) (σ : Equiv.Perm (Fin n))
    (hinv : ∀ y u, Φ y (u ∘ σ) = Φ y u) (x w : E) (u : Fin n → E) :
    fderiv ℝ Φ x w (u ∘ σ) = fderiv ℝ Φ x w u := by sorry
