-- Prove2me | Theorems.Thm_Formalism_DivisionValues_GluingInclusion_conjIdeal_eq
-- name    : Formalism.DivisionValues.GluingInclusion.conjIdeal_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:51.250534+00:00
-- url     : https://prove2.me/theorems/9cfb4317-08dd-4ee6-bc50-3d9bc5288157
-- title:
--   Gluing Inclusion: conj Ideal eq
-- statement:
--   The Gluing Inclusion construction uses the conj Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L209-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L209-L219

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.GluingInclusion.conjIdeal_eq (w : HeightOneSpectrum (𝓞 K)) :
    conjIdeal (K := K) w.asIdeal = (conjPl w).asIdeal := by sorry
