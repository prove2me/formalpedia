-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_inf_lat
-- name    : Formalism.EigenvalueLevelCeiling.idxRules_inf_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:59.493987+00:00
-- url     : https://prove2.me/theorems/22e40ab2-c414-43fa-9c20-a076498eb884
-- title:
--   Eigenvalue Level Ceiling: idx Rules inf lat
-- statement:
--   The Eigenvalue Level Ceiling construction uses the idx Rules inf lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L245-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L245-L260

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

theorem Formalism.EigenvalueLevelCeiling.idxRules_inf_lat {W : Submodule K V} {A B : Submodule R V}
    (hA : A.FG ∧ Submodule.span K (A : Set V) = W) (hB : B.FG ∧ Submodule.span K (B : Set V) = W) :
    (A ⊓ B).FG ∧ Submodule.span K ((A ⊓ B : Submodule R V) : Set V) = W := by sorry
