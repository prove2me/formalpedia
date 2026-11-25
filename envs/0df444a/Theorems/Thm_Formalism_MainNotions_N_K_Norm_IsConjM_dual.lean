-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_K_Norm_IsConjM_dual
-- name    : Formalism.MainNotions.N.K.Norm.IsConjM.dual
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:24.470595+00:00
-- url     : https://prove2.me/theorems/dbf59a42-73ad-45ed-a333-1226713ecf55
-- title:
--   Is Conj M: dual
-- statement:
--   The Is Conj M construction uses the dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L45-L51

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

theorem Formalism.MainNotions.N.K.Norm.IsConjM.dual [Group Γ] {M M' : Γ → Matrix n n K} (h : IsConjM M M') :
    IsConjM (fun g => (M g⁻¹).transpose) (fun g => (M' g⁻¹).transpose) := by sorry
