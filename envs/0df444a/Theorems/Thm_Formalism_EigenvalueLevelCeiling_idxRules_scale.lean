-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_scale
-- name    : Formalism.EigenvalueLevelCeiling.idxRules_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:32.590743+00:00
-- url     : https://prove2.me/theorems/d199f3e7-c27d-4fae-9340-3c4a829798d7
-- title:
--   Eigenvalue Level Ceiling: idx Rules scale
-- statement:
--   The Eigenvalue Level Ceiling construction uses the idx Rules scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L171-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/IdxRules.lean#L171-L197

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

theorem Formalism.EigenvalueLevelCeiling.idxRules_scale [FiniteDimensional K V] (v : HeightOneSpectrum R) (W : Submodule K V)
    (B : Submodule R V) (hB : B.FG ∧ Submodule.span K (B : Set V) = W) {a : K} (ha : a ≠ 0) :
    lidx v.asIdeal B (scG a B) =
      (finrank K W : ℤ) * FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a) := by sorry
