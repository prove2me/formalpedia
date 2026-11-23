-- Prove2me | Theorems.Thm_Formalism_DivisionValues_GluingInclusion_loc_glueLat
-- name    : Formalism.DivisionValues.GluingInclusion.loc_glueLat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:54.782567+00:00
-- url     : https://prove2.me/theorems/daae820e-2af1-49e7-bcad-47af7ee5be54
-- title:
--   Gluing Inclusion: loc glue Lat
-- statement:
--   The Gluing Inclusion construction uses the loc glue Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L243-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondStepGluing.lean#L243-L248

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

theorem Formalism.DivisionValues.GluingInclusion.loc_glueLat {D : ℕ} (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K))
    (hc : ∀ w, L (conjPl w) = L w) (R : Submodule (𝓞 K) (Fin D → K))
    (hR : ∀ w : HeightOneSpectrum (𝓞 K), localization₂ w.asIdeal R = localization₂ w.asIdeal (L w))
    (w : HeightOneSpectrum (𝓞 K)) :
    loc (K := K) w.asIdeal R = loc (K := K) w.asIdeal (L w) := by sorry
