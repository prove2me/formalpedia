-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_lidx_map
-- name    : Formalism.EigenvalueLevelCeiling.idxRules_lidx_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:35.744581+00:00
-- url     : https://prove2.me/theorems/c9b20711-4589-4b34-8f6b-e07955813589
-- title:
--   Eigenvalue Level Ceiling: idx Rules lidx map
-- statement:
--   The Eigenvalue Level Ceiling construction uses the idx Rules lidx map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L118-L126

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

theorem Formalism.EigenvalueLevelCeiling.idxRules_lidx_map (p : Ideal R) [p.IsPrime] (φ : V →ₗ[K] V') (hφ : Function.Injective φ)
    (A B : Submodule R V) :
    lidx p (A.map (φ.restrictScalars R)) (B.map (φ.restrictScalars R)) = lidx p A B := by sorry
