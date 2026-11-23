-- Prove2me | Theorems.Thm_Formalism_DivisionValues_GluingInclusion_glue_spec
-- name    : Formalism.DivisionValues.GluingInclusion.glue_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:09.071793+00:00
-- url     : https://prove2.me/theorems/13fadb8f-37b5-452b-a44c-4f11bf9a8c41
-- title:
--   Gluing Inclusion: glue spec
-- statement:
--   The Gluing Inclusion construction uses the glue spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L74-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L74-L182

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

theorem Formalism.DivisionValues.GluingInclusion.glue_spec (hR : ¬ IsField R) (L0 : Submodule R V) (L : HeightOneSpectrum R → Submodule R V)
    (h0 : Submodule.IsLattice K L0) (hL : ∀ w, Submodule.IsLattice K (L w))
    (hfin : {w : HeightOneSpectrum R | localization₂ w.asIdeal (L w) ≠ localization₂ w.asIdeal L0}.Finite) :
    Submodule.IsLattice K (⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w)) ∧
      ∀ w : HeightOneSpectrum R,
        localization₂ w.asIdeal (⨅ w : HeightOneSpectrum R, localization₂ w.asIdeal (L w)) =
          localization₂ w.asIdeal (L w) := by sorry
