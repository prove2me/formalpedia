-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_coeff_Ps
-- name    : Formalism.L2.FormalSeriesBounds.Sys.coeff_Ps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:59.151344+00:00
-- url     : https://prove2.me/theorems/7562eccf-640d-49f0-bf56-7649652325cd
-- title:
--   Sys: coeff Ps
-- statement:
--   The Sys construction uses the coeff Ps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L144-L145

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

theorem Formalism.L2.FormalSeriesBounds.Sys.coeff_Ps (t : I → MvPowerSeries I C) (c : I) (μ : I →₀ ℕ) :
    coeff μ (S.Ps t c) = Matrix.vecMul (fun x => dl x μ - S.Rr t x μ) S.Mt⁻¹ c := by sorry
