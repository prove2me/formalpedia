-- Prove2me | Theorems.Thm_Formalism_DivisionValues_StepBAux_idx_change_img
-- name    : Formalism.DivisionValues.StepBAux.idx_change_img
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:40.975509+00:00
-- url     : https://prove2.me/theorems/a5f92978-28b5-4ded-b633-dc504fa92348
-- title:
--   Step BAux: idx change img
-- statement:
--   The Step BAux construction uses the idx change img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L379-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L379-L398

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

theorem Formalism.DivisionValues.StepBAux.idx_change_img (hIC : IdxChange) {d : ℕ} (ι0 ι1 : Matrix (Fin d) (Fin d) K)
    (hι0 : IsUnit ι0.det) (hι1 : IsUnit ι1.det) (L0 L1 : Submodule (𝓞 K) (Fin d → K))
    (hL1 : Submodule.IsLattice K L1) (w : HeightOneSpectrum (𝓞 K))
    (e0 e1 : Fin d → Fin d → K) (he0 : IsLocBasis L0 w e0) (he1 : IsLocBasis L1 w e1) :
    ∃ γ : Matrix (Fin d) (Fin d) K,
      (fun i => ι1 *ᵥ e1 i) = (fun i => ∑ k, γ k i • (ι0 *ᵥ e0 k)) ∧
      idx w (matLat ι0 L0) (matLat ι1 L1) = vw w γ.det ∧
      idx (conjPl w) (matLat ι0 L0) (matLat ι1 L1) = vw (conjPl w) γ.det := by sorry
