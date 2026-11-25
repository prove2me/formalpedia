-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_ze_partial
-- name    : Formalism.L2.FormalSeriesBounds.Sys.ze_partial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:27:28.73644+00:00
-- url     : https://prove2.me/theorems/d077a2e0-198a-49a1-82c4-1fe6adc63dfc
-- title:
--   Sys: ze partial
-- statement:
--   The Sys construction uses the ze partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L439-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L439-L460

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
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

theorem Formalism.L2.FormalSeriesBounds.Sys.ze_partial {t : I → MvPowerSeries I C} (ht : S.IsT t) (κ : J) (N : ℕ) (μ : I →₀ ℕ)
    (hμ : μ.degree ≤ N) :
    coeff μ (S.ze t κ) =
      coeff μ (-∑ s ∈ Finset.Icc 1 N, ∑ c : I, S.be c s κ • t c ^ (V.l ^ s)) := by sorry
