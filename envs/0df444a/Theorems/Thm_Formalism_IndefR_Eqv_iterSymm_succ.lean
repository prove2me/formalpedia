-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_iterSymm_succ
-- name    : Formalism.IndefR.Eqv.iterSymm_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:24.670348+00:00
-- url     : https://prove2.me/theorems/14a4e97e-f211-4b80-8376-bb67d789700a
-- title:
--   Eqv: iter Symm succ
-- statement:
--   The Eqv construction uses the iter Symm succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L67-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/SobSym.lean#L67-L104

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

theorem Formalism.IndefR.Eqv.iterSymm_succ (m : ℕ) (IH : ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (g : E → H),
    ContDiff ℝ ∞ g → ∀ (x : E) (v : Fin (m + 1) → E) (σ : Equiv.Perm (Fin (m + 1))),
      iteratedFDeriv ℝ (m + 1) g x (v ∘ σ) = iteratedFDeriv ℝ (m + 1) g x v)
    (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (g : E → H) (hg : ContDiff ℝ ∞ g) (x : E)
    (v : Fin (m + 2) → E) (σ : Equiv.Perm (Fin (m + 2))) :
    iteratedFDeriv ℝ (m + 2) g x (v ∘ σ) = iteratedFDeriv ℝ (m + 2) g x v := by sorry
