-- Prove2me | Theorems.Thm_Formalism_DivisionValues_GluingInclusion_loc_eq
-- name    : Formalism.DivisionValues.GluingInclusion.loc_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:43.950971+00:00
-- url     : https://prove2.me/theorems/91163365-1824-40df-8553-ea7cc878f152
-- title:
--   Gluing Inclusion: loc eq
-- statement:
--   The Gluing Inclusion construction uses the loc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L221-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L221-L229

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

theorem Formalism.DivisionValues.GluingInclusion.loc_eq (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (A : Submodule (𝓞 K) (Fin d → K)) :
    loc (K := K) w.asIdeal A = localization₂ w.asIdeal A ⊓ localization₂ (conjPl w).asIdeal A := by sorry
