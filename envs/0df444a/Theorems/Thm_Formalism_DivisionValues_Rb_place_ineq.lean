-- Prove2me | Theorems.Thm_Formalism_DivisionValues_Rb_place_ineq
-- name    : Formalism.DivisionValues.Rb.place_ineq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:51.730336+00:00
-- url     : https://prove2.me/theorems/72d067fc-9259-4262-a919-32aa3de006db
-- title:
--   Rb: place ineq
-- statement:
--   The Rb construction uses the place ineq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaSecond.lean#L133-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionLemmaSecond.lean#L133-L157

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DeterminantCauchySchwarz
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaSecond
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
open Formalism.DivisionValues.Rb
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.Rb.place_ineq (hCS : DetCS) (K0 : Subfield K) (hK0 : IsCMSub K0) {n D : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ K0)
    (hHpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef)
    (P : Matrix (Fin D) (Fin n) K) (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hXQ : IsQuotMetric P H XQ) (hc : (P * H⁻¹ * Pᴴ).det ≠ 0) (v : InfinitePlace K) :
    (metMat XQ v).det.re * (metMat XQ (plc v)).det.re ≤
      (‖v.embedding (P * H⁻¹ * Pᴴ).det‖ ^ 2)⁻¹ := by sorry
