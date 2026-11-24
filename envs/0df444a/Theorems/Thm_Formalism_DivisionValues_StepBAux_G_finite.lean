-- Prove2me | Theorems.Thm_Formalism_DivisionValues_StepBAux_G_finite
-- name    : Formalism.DivisionValues.StepBAux.G_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:14.626412+00:00
-- url     : https://prove2.me/theorems/82ae4284-a09c-43ec-b395-2192acfefb7b
-- title:
--   Step BAux: G finite
-- statement:
--   The Step BAux construction uses the G finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L570-L615
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L570-L615

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
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
open Formalism.DivisionValues.StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.StepBAux.G_finite (hV : ValBasic) (hIC : IdxChange) (hLB : LcvBasis) (hPF : ProdFormula)
    [IsTotallyComplex K] (v0 : InfinitePlace K) (hv0 : IsConjAt v0) (D : ℕ)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXQ : ∀ v, IsUnit (XQ v).det)
    (abelian₂ : Submodule (𝓞 K) (Fin D → K)) (hLam : Submodule.IsLattice K abelian₂)
    (G : HeightOneSpectrum (𝓞 K) → K) (e : HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K)
    (he : ∀ w, IsLocBasis abelian₂ w (e w)) (hG : ∀ w, v0.embedding (G w) = (gram XQ v0 (e w)).det) :
    (Function.support fun w => lw w * (vw w (G w) : ℝ)).Finite := by sorry
