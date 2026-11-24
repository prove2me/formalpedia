-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_eqn_eq
-- name    : Formalism.L2.FormalSeriesBounds.Sys.eqn_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:58.542231+00:00
-- url     : https://prove2.me/theorems/32857195-914d-45a7-8128-a32f8a61e99e
-- title:
--   Sys: eqn eq
-- statement:
--   The Sys construction uses the eqn eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L188-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L188-L197

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
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
  {X : Cart V d I J}
open Formalism.L2.FormalSeriesBounds.Sys
variable (S : Sys X)

theorem Formalism.L2.FormalSeriesBounds.Sys.eqn_eq (t : I → MvPowerSeries I C) (x : I) (μ : I →₀ ℕ) :
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ c : I,
        S.al c s x * MvPowerSeries.coeff μ (t c ^ (V.l ^ s))) =
      Matrix.vecMul (fun c => coeff μ (t c)) S.Mt x + S.Rr t x μ := by sorry
