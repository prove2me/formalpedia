-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_herm_of_hermAt
-- name    : Formalism.DivisionValues.ConjugateWeightGram.herm_of_hermAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:12:02.875818+00:00
-- url     : https://prove2.me/theorems/61bd010f-8370-4623-a37e-1fbd9cc3cd64
-- title:
--   Conjugate Weight Gram: herm of herm At
-- statement:
--   The Conjugate Weight Gram construction uses the herm of herm At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L139-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L139-L148

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

theorem Formalism.DivisionValues.ConjugateWeightGram.herm_of_hermAt {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ}
    (hR : IsHermAt v0 H X) (i j : Fin n) : H j i = star (H i j) := by sorry
