-- Prove2me | Theorems.Thm_Formalism_DivisionValues_StepBAux_local_id
-- name    : Formalism.DivisionValues.StepBAux.local_id
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:48.832914+00:00
-- url     : https://prove2.me/theorems/6bec0145-edaa-4f54-9217-2c0f5f4f6b66
-- title:
--   Step BAux: local id
-- statement:
--   The Step BAux construction uses the local id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L400-L543
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionSecondStep.lean#L400-L543

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

theorem Formalism.DivisionValues.StepBAux.local_id (hV : ValBasic) (hIC : IdxChange) (hJw : JwGram) [IsTotallyComplex K]
    (K0 : Subfield K) (hK0 : IsCMSub K0) (v0 : InfinitePlace K) (hv0 : IsConjAt v0)
    (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXE : ∀ v, IsUnit (XE v).det)
    (XQ0 XQ1 : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXQ0 : ∀ v, IsUnit (XQ0 v).det)
    (hXQ1 : ∀ v, IsUnit (XQ1 v).det)
    (Lam0 Lam1 : Submodule (𝓞 K) (Fin D → K)) (hL1 : Submodule.IsLattice K Lam1)
    (ι0 ι1 : Matrix (Fin D) (Fin D) K) (hι0 : IsUnit ι0.det) (hι1 : IsUnit ι1.det)
    (J : Type) [Fintype J] (d : J → ℕ)
    (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (hXW : ∀ j v, IsUnit (XW j v).det)
    (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)) (hM : ∀ j, Submodule.IsLattice K (M j))
    (HT0 HT1 : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K)
    (XT0 XT1 : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (hHT0 : ∀ j, IsRatHerm K0 (HT0 j) (XT0 j)) (hHT1 : ∀ j, IsRatHerm K0 (HT1 j) (XT1 j))
    (T0 T1 : ∀ j, Submodule (𝓞 K) (Fin (d j) → K))
    (hT0 : ∀ j, Submodule.IsLattice K (T0 j)) (hT1 : ∀ j, Submodule.IsLattice K (T1 j))
    (θ0 θ1 : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K) (hθ0 : ∀ j, IsUnit (θ0 j).det)
    (hθ1 : ∀ j, IsUnit (θ1 j).det)
    (κ0 ρr : ℝ) (hκ : 0 < κ0) (ρ : K) (hρ : v0.embedding ρ = (ρr : ℂ)) (hρpos : 0 < ρr)
    (w : HeightOneSpectrum (𝓞 K)) (hρv : vw w ρ = 0)
    (hdet0 : detRatio XQ0 XE ι0 v0 = κ0 ^ D * ∏ j, detRatio (XT0 j) (XW j) (θ0 j) v0)
    (hdet1 : detRatio XQ1 XE ι1 v0 = (κ0 * ρr) ^ D * ∏ j, detRatio (XT1 j) (XW j) (θ1 j) v0)
    (G0 G1 : K) (e0 e1 : Fin D → Fin D → K) (he0 : IsLocBasis Lam0 w e0)
    (he1 : IsLocBasis Lam1 w e1)
    (hG0 : v0.embedding G0 = (gram XQ0 v0 e0).det) (hG1 : v0.embedding G1 = (gram XQ1 v0 e1).det)
    (f0 f1 : ∀ j, Fin (d j) → Fin (d j) → K) (hf0 : ∀ j, IsLocBasis (T0 j) w (f0 j))
    (hf1 : ∀ j, IsLocBasis (T1 j) w (f1 j)) :
    idx w (matLat ι0 Lam0) (matLat ι1 Lam1) + idx (conjPl w) (matLat ι0 Lam0) (matLat ι1 Lam1) =
      vw w G1 - vw w G0 + ∑ j, ((idx w (M j) (matLat (θ1 j) (T1 j)) -
          idx w (M j) (matLat (θ0 j) (T0 j))) +
        (idx (conjPl w) (M j) (matLat (θ1 j) (T1 j)) -
          idx (conjPl w) (M j) (matLat (θ0 j) (T0 j))) +
        (jw (HT1 j) w (T1 j) - jw (HT0 j) w (T0 j))) := by sorry
