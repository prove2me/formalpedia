-- Prove2me | Theorems.Thm_Formalism_DivisionValues_opNormAt_pos_alt
-- name    : Formalism.DivisionValues.opNormAt_pos_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:32.319812+00:00
-- url     : https://prove2.me/theorems/5e20aa13-9721-49bc-a108-0f50ae638503
-- title:
--   Division Values: op Norm At pos alt
-- statement:
--   The Division Values construction uses the op Norm At pos alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L269-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L269-L295

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
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
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.DivisionValues.opNormAt_pos_alt [StarRing K] {n D : ℕ}
    (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (Y : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (v : InfinitePlace K)
    (hXN : IsUnit (XN v).det) (hY : IsUnit (Y v).det)
    (φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K)) (hφ : φ ≠ 0) :
    0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis Y v φ := by sorry
