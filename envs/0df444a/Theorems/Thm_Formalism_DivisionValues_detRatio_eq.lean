-- Prove2me | Theorems.Thm_Formalism_DivisionValues_detRatio_eq
-- name    : Formalism.DivisionValues.detRatio_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:39.908856+00:00
-- url     : https://prove2.me/theorems/c4bfd72e-a227-465a-8c61-a05d97a0776d
-- title:
--   Division Values: det Ratio eq
-- statement:
--   The Division Values construction uses the det Ratio eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean#L63-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean#L63-L76

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.detRatio_eq {d : ℕ} (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (φ : Matrix (Fin d) (Fin d) K) (v : InfinitePlace K) :
    detRatio XS XT φ v =
      ((φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding).det.re / (metMat XS v).det.re := by sorry
