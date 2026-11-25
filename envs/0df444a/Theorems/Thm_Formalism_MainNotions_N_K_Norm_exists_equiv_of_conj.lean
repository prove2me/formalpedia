-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_K_Norm_exists_equiv_of_conj
-- name    : Formalism.MainNotions.N.K.Norm.exists_equiv_of_conj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:07.261506+00:00
-- url     : https://prove2.me/theorems/620a02ec-510a-45cd-a2eb-190183409028
-- title:
--   Norm: exists equiv of conj
-- statement:
--   The Norm construction uses the exists equiv of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L73-L77

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

theorem Formalism.MainNotions.N.K.Norm.exists_equiv_of_conj {M M' : Γ →* Matrix (Fin k) (Fin k) K} (h : IsConjM ⇑M ⇑M') :
    ∃ e : (Fin k → K) ≃ₗ[K] (Fin k → K), ∀ g v, e (matRep M g v) = matRep M' g (e v) := by sorry
