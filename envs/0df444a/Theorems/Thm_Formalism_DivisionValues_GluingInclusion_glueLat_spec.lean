-- Prove2me | Theorems.Thm_Formalism_DivisionValues_GluingInclusion_glueLat_spec
-- name    : Formalism.DivisionValues.GluingInclusion.glueLat_spec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:36:18.202818+00:00
-- url     : https://prove2.me/theorems/710eae6d-f020-499e-a3ba-b6150e4a16b5
-- title:
--   Gluing Inclusion: glue Lat spec
-- statement:
--   The Gluing Inclusion construction uses the glue Lat spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L190-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L190-L196

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

theorem Formalism.DivisionValues.GluingInclusion.glueLat_spec {D : ℕ} (L0 : Submodule (𝓞 K) (Fin D → K))
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K))
    (h0 : Submodule.IsLattice K L0) (hL : ∀ w, Submodule.IsLattice K (L w))
    (hfin : {w : HeightOneSpectrum (𝓞 K) | localization₂ w.asIdeal (L w) ≠ localization₂ w.asIdeal L0}.Finite) :
    Submodule.IsLattice K (glueLat L) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), localization₂ w.asIdeal (glueLat L) = localization₂ w.asIdeal (L w) := by sorry
