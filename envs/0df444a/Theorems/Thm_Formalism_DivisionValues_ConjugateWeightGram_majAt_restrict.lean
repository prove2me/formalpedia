-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_majAt_restrict
-- name    : Formalism.DivisionValues.ConjugateWeightGram.majAt_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:12:32.151794+00:00
-- url     : https://prove2.me/theorems/71500b7e-db25-4a3b-867f-7c34c302db4e
-- title:
--   Conjugate Weight Gram: maj At restrict
-- statement:
--   The Conjugate Weight Gram construction uses the maj At restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L765-L783
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L765-L783

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

theorem Formalism.DivisionValues.ConjugateWeightGram.majAt_restrict {K0 : Subfield K} {n d : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hH : IsRatHerm K0 H X)
    (z : Fin d → Fin n → K) (XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (hXT : ((XT v)⁻¹)ᴴ * (XT v)⁻¹ =
      ((colMat z).map v.embedding)ᴴ * (H.map v.embedding) * (colMat z).map v.embedding)
    (x y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (comb z x) (comb z y) := by sorry
