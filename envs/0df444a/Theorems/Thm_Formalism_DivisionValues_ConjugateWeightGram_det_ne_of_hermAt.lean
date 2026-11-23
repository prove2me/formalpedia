-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_det_ne_of_hermAt
-- name    : Formalism.DivisionValues.ConjugateWeightGram.det_ne_of_hermAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:12:31.197411+00:00
-- url     : https://prove2.me/theorems/e5ee0531-9fca-49ef-bf68-161ad36452e8
-- title:
--   Conjugate Weight Gram: det ne of herm At
-- statement:
--   The Conjugate Weight Gram construction uses the det ne of herm At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L150-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L150-L159

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
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
open RationalHermitianForm
open Formalism.DivisionValues.ConjugateWeightGram
open StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.ConjugateWeightGram.det_ne_of_hermAt {v0 : InfinitePlace K} {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ}
    (hR : IsHermAt v0 H X) : H.det ≠ 0 := by sorry
