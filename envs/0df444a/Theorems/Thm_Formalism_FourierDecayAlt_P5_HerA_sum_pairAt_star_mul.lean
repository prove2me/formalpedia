-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_sum_pairAt_star_mul
-- name    : Formalism.FourierDecayAlt.P5.HerA.sum_pairAt_star_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:40:57.493799+00:00
-- url     : https://prove2.me/theorems/cee1a464-5868-4f17-8240-884f022d03fb
-- title:
--   Her A: sum pair At star mul
-- statement:
--   The Her A construction uses the sum pair At star mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L187-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L187-L204

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumPairAtStarMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
variable {μ : Measure (Mt k r)} {U : Submodule ℂ (RadSp k r z z' π π')}

theorem Formalism.FourierDecayAlt.P5.HerA.sum_pairAt_star_mul {hU : IntOn μ U} (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')))
    (hM : ∀ a b, M a b ∈ adjAlg μ U hU) (hN : ∀ a b, N a b ∈ adjAlg μ U hU)
    (x y : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (hy : ∀ a, y a ∈ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    ∑ a, pairAt μ (act (star M * N) x a) (y a) c = ∑ e, pairAt μ (act N x e) (act M y e) c := by sorry
