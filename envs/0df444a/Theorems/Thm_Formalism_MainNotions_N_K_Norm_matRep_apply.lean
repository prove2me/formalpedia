-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_K_Norm_matRep_apply
-- name    : Formalism.MainNotions.N.K.Norm.matRep_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:19.652856+00:00
-- url     : https://prove2.me/theorems/df596499-ed11-4010-90cb-a6da04e1e9fc
-- title:
--   Norm: mat Rep apply
-- statement:
--   The Norm construction uses the mat Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L59-L61

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

theorem Formalism.MainNotions.N.K.Norm.matRep_apply (M : Γ →* Matrix (Fin k) (Fin k) K) (g : Γ) (v : Fin k → K) :
    matRep M g v = (M g).mulVec v := by sorry
