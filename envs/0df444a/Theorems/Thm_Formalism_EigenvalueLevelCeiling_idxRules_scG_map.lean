-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_scG_map
-- name    : Formalism.EigenvalueLevelCeiling.idxRules_scG_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:16.468269+00:00
-- url     : https://prove2.me/theorems/94565e3e-5f39-4cf6-bb52-8206364669e6
-- title:
--   Eigenvalue Level Ceiling: idx Rules sc G map
-- statement:
--   The Eigenvalue Level Ceiling construction uses the idx Rules sc G map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L149-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L149-L155

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']

theorem Formalism.EigenvalueLevelCeiling.idxRules_scG_map (a : K) (φ : V →ₗ[K] V') (A : Submodule R V) :
    scG a (A.map (φ.restrictScalars R)) = (scG a A).map (φ.restrictScalars R) := by sorry
