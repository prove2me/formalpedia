-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_mul_mem_entries
-- name    : Formalism.FourierDecayAlt.P5.HerA.mul_mem_entries
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:41:00.600433+00:00
-- url     : https://prove2.me/theorems/3d247889-a841-4c17-ac1c-a06e55c03318
-- title:
--   Her A: mul mem entries
-- statement:
--   The Her A construction uses the mul mem entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L182-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L182-L185

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

theorem Formalism.FourierDecayAlt.P5.HerA.mul_mem_entries {hU : IntOn μ U} (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ adjAlg μ U hU)
    (hN : ∀ a b, N a b ∈ adjAlg μ U hU) (a b : Ix S) : (M * N) a b ∈ adjAlg μ U hU := by sorry
