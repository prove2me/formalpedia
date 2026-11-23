-- Prove2me | Theorems.Thm_Formalism_DivisionValues_metMat_det_re_ne
-- name    : Formalism.DivisionValues.metMat_det_re_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:04.424707+00:00
-- url     : https://prove2.me/theorems/0130d911-358f-462e-89ff-3135e6769f15
-- title:
--   Division Values: met Mat det re ne
-- statement:
--   The Division Values construction uses the met Mat det re ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean#L78-L85

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

theorem Formalism.DivisionValues.metMat_det_re_ne {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (hX : IsUnit (X v).det) : (metMat X v).det.re ≠ 0 := by sorry
