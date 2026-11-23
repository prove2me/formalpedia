-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_map_gramMat
-- name    : Formalism.DivisionValues.ConjugateWeightGram.map_gramMat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:12:31.447774+00:00
-- url     : https://prove2.me/theorems/ad2c5abe-e24a-43c8-8735-aaed294d5679
-- title:
--   Conjugate Weight Gram: map gram Mat
-- statement:
--   The Conjugate Weight Gram construction uses the map gram Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L719-L727
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L719-L727

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

theorem Formalism.DivisionValues.ConjugateWeightGram.map_gramMat {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (z : Fin d → Fin n → K) (σ : K →+* ℂ)
    (hz : ∀ a i, σ (star (z a i)) = starRingEnd ℂ (σ (z a i))) :
    (gramMat H z).map σ = ((colMat z).map σ)ᴴ * (H.map σ) * (colMat z).map σ := by sorry
