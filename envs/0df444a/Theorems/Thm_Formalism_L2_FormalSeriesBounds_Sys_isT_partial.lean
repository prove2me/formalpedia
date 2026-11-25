-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_isT_partial
-- name    : Formalism.L2.FormalSeriesBounds.Sys.isT_partial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:26:17.744841+00:00
-- url     : https://prove2.me/theorems/c11fc2d7-9679-5055-b8b2-85c49d1b6a01
-- title:
--   Sys: is T partial
-- statement:
--   The Sys construction uses the is T partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L419-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L419-L437

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)

theorem Formalism.L2.FormalSeriesBounds.Sys.isT_partial {t : I → MvPowerSeries I C} (ht : S.IsT t) (x : I) (N : ℕ) (μ : I →₀ ℕ)
    (hμ : μ.degree ≤ N) :
    coeff μ (∑ s ∈ Finset.range (N + 1), ∑ c : I, S.al c s x • t c ^ (V.l ^ s)) =
      coeff μ (X x : MvPowerSeries I C) := by sorry
