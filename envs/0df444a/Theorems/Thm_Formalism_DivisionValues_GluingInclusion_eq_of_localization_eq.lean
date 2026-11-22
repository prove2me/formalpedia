-- Prove2me | Theorems.Thm_Formalism_DivisionValues_GluingInclusion_eq_of_localization_eq
-- name    : Formalism.DivisionValues.GluingInclusion.eq_of_localization_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:36:00.489803+00:00
-- url     : https://prove2.me/theorems/b706dfec-da80-4418-88e0-7db04093aef2
-- title:
--   Gluing Inclusion: eq of localization eq
-- statement:
--   The Gluing Inclusion construction uses the eq of localization eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L198-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L198-L201

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
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.DivisionValues.GluingInclusion.eq_of_localization_eq {D : ℕ} (R R' : Submodule (𝓞 K) (Fin D → K))
    (h : ∀ w : HeightOneSpectrum (𝓞 K), localization₂ w.asIdeal R = localization₂ w.asIdeal R') : R = R' := by sorry
