-- Prove2me | Theorems.Thm_Formalism_DivisionValues_StepBAux_localization_eq_and_conj_eq_of_semilocalization_eq
-- name    : Formalism.DivisionValues.StepBAux.localization_eq_and_conj_eq_of_semilocalization_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:04:07.009526+00:00
-- url     : https://prove2.me/theorems/cd9c92b1-851c-459f-b6c4-e2906c195efa
-- title:
--   Step BAux: localization eq and conj eq of semilocalization eq
-- statement:
--   The Step BAux construction uses the localization eq and conj eq of semilocalization eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L249-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L249-L259

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.StepBAux.localization_eq_and_conj_eq_of_semilocalization_eq (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (A B : Submodule (𝓞 K) (Fin d → K))
    (h : Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal A = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B ∧
      Formalism.HermitianLatticesTheory.localization₂ (conjPl w).asIdeal A = Formalism.HermitianLatticesTheory.localization₂ (conjPl w).asIdeal B := by sorry
