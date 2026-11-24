-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_K_Norm_IsConjM_comp
-- name    : Formalism.MainNotions.N.K.Norm.IsConjM.comp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:26:34.304793+00:00
-- url     : https://prove2.me/theorems/d91164dc-694e-4232-bb99-840d3d7224ca
-- title:
--   Is Conj M: comp
-- statement:
--   The Is Conj M construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L27-L30

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

theorem Formalism.MainNotions.N.K.Norm.IsConjM.comp {M M' : Γ → Matrix n n K} (h : IsConjM M M') {Γ' : Type} (f : Γ' → Γ) :
    IsConjM (fun g => M (f g)) (fun g => M' (f g)) := by sorry
