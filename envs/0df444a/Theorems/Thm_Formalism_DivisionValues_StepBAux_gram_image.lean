-- Prove2me | Theorems.Thm_Formalism_DivisionValues_StepBAux_gram_image
-- name    : Formalism.DivisionValues.StepBAux.gram_image
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:19.599592+00:00
-- url     : https://prove2.me/theorems/d1e0ce9e-2dbe-4771-90d9-ef07208769f4
-- title:
--   Step BAux: gram image
-- statement:
--   The Step BAux construction uses the gram image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L125-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L125-L145

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

theorem Formalism.DivisionValues.StepBAux.gram_image [IsTotallyComplex K] {d : ℕ}
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hXS : ∀ v, IsUnit (XS v).det)
    (φ : Matrix (Fin d) (Fin d) K) (e : Fin d → Fin d → K) (v : InfinitePlace K) :
    (gram XT v (fun i => φ *ᵥ e i)).det = (detRatio XS XT φ v : ℂ) * (gram XS v e).det := by sorry
