-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_first_kernel_inner_sum
-- name    : Formalism.FourierDecayAlt.P.A5x6.first_kernel_inner_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:14.469068+00:00
-- url     : https://prove2.me/theorems/6bf45f04-a91f-4890-8872-ec0efa66a272
-- title:
--   A5x6: first kernel inner sum
-- statement:
--   The A5x6 construction uses the first kernel inner sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L326-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L326-L396

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6

theorem Formalism.FourierDecayAlt.P.A5x6.first_kernel_inner_sum {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
    (hψ : ∀ r ∈ R, ψ r = 1) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det)
    (hC : Finite (coker R Z)) (hC' : Finite (coker R Z')) (hD : Finite (coker R Z →ₗ[R] KR R))
    (hOD1 : ∀ x : coker R Z, x = 0 →
      ∑ᶠ α : coker R Z →ₗ[R] KR R, psiKR R ψ (α x) = (Nat.card (coker R Z) : ℂ))
    (hOD2 : ∀ x : coker R Z, x ≠ 0 → ∑ᶠ α : coker R Z →ₗ[R] KR R, psiKR R ψ (α x) = 0)
    (hO1 : ∀ μ : coker R Z →ₗ[R] KR R, μ = 0 →
      ∑ᶠ β : coker R Z, psiKR R ψ (μ β) = (Nat.card (coker R Z) : ℂ))
    (hO2 : ∀ μ : coker R Z →ₗ[R] KR R, μ ≠ 0 → ∑ᶠ β : coker R Z, psiKR R ψ (μ β) = 0)
    {X : Type} (κ : X → K)
    (hκ : Function.Bijective (fun x => (Submodule.Quotient.mk (κ x) : KR R))) :
    (Function.support fun x => singleBlockInner R ψ Z Z' (κ x)).Finite ∧
      ∑ᶠ x, singleBlockInner R ψ Z Z' (κ x) = (Nat.card (coker R Z) : ℂ) * (Nat.card (coker R Z') : ℂ) *
        (Nat.card (isoZZ R Z Z') : ℂ) := by sorry
