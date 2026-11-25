-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_K_Norm_IsConjM_smul
-- name    : Formalism.MainNotions.N.K.Norm.IsConjM.smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:18.088165+00:00
-- url     : https://prove2.me/theorems/086cc6ae-c01b-50ef-b619-f46df182ffc5
-- title:
--   Is Conj M: smul
-- statement:
--   The Is Conj M construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L40-L43

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
variable {Γ : Type} {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.MainNotions.N.K.Norm.IsConjM.smul {M M' : Γ → Matrix n n K} (h : IsConjM M M') (c : Γ → K) :
    IsConjM (fun g => c g • M g) (fun g => c g • M' g) := by sorry
