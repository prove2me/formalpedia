-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_K_Norm_matEquiv_apply
-- name    : Formalism.MainNotions.N.K.Norm.matEquiv_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:24:47.817322+00:00
-- url     : https://prove2.me/theorems/20fbbaec-25c7-4a8e-a174-787aa629b8f1
-- title:
--   Norm: mat Equiv apply
-- statement:
--   The Norm construction uses the mat Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L70-L71

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {Γ : Type} [Group Γ] {K : Type} [CommRing K] {k : ℕ}

theorem Formalism.MainNotions.N.K.Norm.matEquiv_apply (P Q : Matrix (Fin k) (Fin k) K) (h1 : P * Q = 1) (h2 : Q * P = 1) (v : Fin k → K) :
    matEquiv P Q h1 h2 v = P.mulVec v := by sorry
