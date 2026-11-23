-- Prove2me | Theorems.Thm_Formalism_DivisionValues_opNormAt_scale_alt
-- name    : Formalism.DivisionValues.opNormAt_scale_alt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:39.94425+00:00
-- url     : https://prove2.me/theorems/5e3a6315-cc4c-426c-98ce-28e360b81cb8
-- title:
--   Division Values: op Norm At scale alt
-- statement:
--   The Division Values construction uses the op Norm At scale alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L258-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L258-L267

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

theorem Formalism.DivisionValues.opNormAt_scale_alt [StarRing K] {n D : ℕ} (s : ℝ) (hs : 0 < s)
    (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (Y Y' : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (v : InfinitePlace K)
    (hY : IsUnit (Y v).det) (hY' : Y' v = ((s : ℝ) : ℂ) • Y v)
    (φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K)) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis Y' v φ =
      s⁻¹ * Formalism.HN.opNormAt (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis Y v φ := by sorry
