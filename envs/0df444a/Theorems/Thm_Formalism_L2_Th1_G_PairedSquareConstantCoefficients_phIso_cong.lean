-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_PairedSquareConstantCoefficients_phIso_cong
-- name    : Formalism.L2.Th1.G.PairedSquareConstantCoefficients.phIso_cong
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:59.369207+00:00
-- url     : https://prove2.me/theorems/bb4c2669-5e7a-5d23-a6c8-cb42939fc917
-- title:
--   Paired Square Constant Coefficients: ph Iso cong
-- statement:
--   The Paired Square Constant Coefficients construction uses the ph Iso cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ConstantCoeffCMulSqSum.lean#L98-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ConstantCoeffCMulSqSum.lean#L98-L130

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ConstantCoeffCMulSqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.L2.Th1.G.PairedSquareConstantCoefficients
variable {K : Type} [Field K]
variable [CharZero K]

theorem Formalism.L2.Th1.G.PairedSquareConstantCoefficients.phIso_cong (R : Subring K) {l linv ph : PowerSeries K} (hF : Frame R l linv ph)
    (h1 : F1 R l linv ph) {O : Type} [CommRing O] [StarRing O] (τ : O →+* K)
    (hE : ∀ α, EndInt R l linv (τ α)) (hB : ∀ z : O, star z = z → IsBinomScalar R (τ z))
    (hN : ∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α)))
    (hA : ∀ α : O, AdjAt R l linv ph (τ α) (τ (star α)))
    {m ν : Type} [Fintype m] [Fintype ν] [DecidableEq ν] (g : ν → O) (δ : m → ν → O)
    (hδ : ∀ a b, ∑ i, star (δ i a) * δ i b = if a = b then g a else 0) :
    Cong R (phIso τ l linv ph δ) (phSum (fun a => τ (g a)) ph) := by sorry
