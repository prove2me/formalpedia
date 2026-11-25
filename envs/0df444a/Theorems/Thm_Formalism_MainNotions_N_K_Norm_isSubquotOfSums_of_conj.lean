-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_K_Norm_isSubquotOfSums_of_conj
-- name    : Formalism.MainNotions.N.K.Norm.isSubquotOfSums_of_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:34.358637+00:00
-- url     : https://prove2.me/theorems/9c72806d-cf75-5074-ac5d-e385b387bce1
-- title:
--   Norm: is Subquot Of Sums of conj
-- statement:
--   The Norm construction uses the is Subquot Of Sums of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L211-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AdmissibleDesigns/InvariantsEqBotIff.lean#L211-L237

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
variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]
  (ρ : Representation LL G V) {ι : Type} {k : ℕ}

theorem Formalism.MainNotions.N.K.Norm.isSubquotOfSums_of_conj (Ms Ms' : ι → G → Matrix (Fin k) (Fin k) LL) (hc : ∀ x, IsConjM (Ms x) (Ms' x))
    (h : IsSubquotOfSums ρ Ms') : IsSubquotOfSums ρ Ms := by sorry
