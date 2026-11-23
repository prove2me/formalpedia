-- Prove2me | Theorems.Thm_Formalism_DivisionValues_StepBAux_isLocBasis_image
-- name    : Formalism.DivisionValues.StepBAux.isLocBasis_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:34.7258+00:00
-- url     : https://prove2.me/theorems/281ef90e-74a6-445c-a5ca-19beb3e03d52
-- title:
--   Step BAux: is Loc Basis image
-- statement:
--   The Step BAux construction uses the is Loc Basis image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L228-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L228-L234

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

theorem Formalism.DivisionValues.StepBAux.isLocBasis_image {d : ℕ} (φ : Matrix (Fin d) (Fin d) K) (hφ : IsUnit φ.det)
    (L : Submodule (𝓞 K) (Fin d → K)) (w : HeightOneSpectrum (𝓞 K)) (e : Fin d → Fin d → K)
    (he : IsLocBasis L w e) : IsLocBasis (matLat φ L) w (fun i => φ *ᵥ e i) := by sorry
