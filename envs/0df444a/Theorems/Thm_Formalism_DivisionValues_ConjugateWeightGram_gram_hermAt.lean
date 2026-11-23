-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_gram_hermAt
-- name    : Formalism.DivisionValues.ConjugateWeightGram.gram_hermAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:08.456499+00:00
-- url     : https://prove2.me/theorems/cdf4893d-e79a-4ad5-beb9-12fde8eca5ae
-- title:
--   Conjugate Weight Gram: gram herm At
-- statement:
--   The Conjugate Weight Gram construction uses the gram herm At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L161-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L161-L172

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

theorem Formalism.DivisionValues.ConjugateWeightGram.gram_hermAt {d : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v0 : InfinitePlace K) (hv0 : IsConjAt v0) (hH : IsHermAt v0 H X) (f : Fin d → Fin d → K) :
    (gram X v0 f).det = v0.embedding (gramR H f) := by sorry
