-- Prove2me | Theorems.Thm_Formalism_DivisionValues_GluingInclusion_sep
-- name    : Formalism.DivisionValues.GluingInclusion.sep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:49.385825+00:00
-- url     : https://prove2.me/theorems/28403caf-926f-46f2-9fa4-1b32fa76100a
-- title:
--   Gluing Inclusion: sep
-- statement:
--   The Gluing Inclusion construction uses the sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L48-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L48-L66

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

theorem Formalism.DivisionValues.GluingInclusion.sep (w : HeightOneSpectrum R) (c : R) (hc : c ≠ 0) :
    ∃ s, s ∉ w.asIdeal ∧ ∀ w' : HeightOneSpectrum R, w' ≠ w → ∃ t, t ∉ w'.asIdeal ∧ c ∣ t * s := by sorry
