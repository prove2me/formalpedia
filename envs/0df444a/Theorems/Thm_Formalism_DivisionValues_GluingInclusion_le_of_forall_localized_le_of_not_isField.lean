-- Prove2me | Theorems.Thm_Formalism_DivisionValues_GluingInclusion_le_of_forall_localized_le_of_not_isField
-- name    : Formalism.DivisionValues.GluingInclusion.le_of_forall_localized_le_of_not_isField
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:31.161339+00:00
-- url     : https://prove2.me/theorems/142d39ab-e068-412b-a9cc-7e89bd30fc57
-- title:
--   Gluing Inclusion: le of forall localized le of not is Field
-- statement:
--   The Gluing Inclusion construction uses the le of forall localized le of not is Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L44-L46

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.GluingInclusion
open Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.DivisionValues.GluingInclusion.le_of_forall_localized_le_of_not_isField (hR : ¬ IsField R) (A B : Submodule R V)
    (h : ∀ w : HeightOneSpectrum R, localization₂ w.asIdeal A ≤ localization₂ w.asIdeal B) : A ≤ B := by sorry
