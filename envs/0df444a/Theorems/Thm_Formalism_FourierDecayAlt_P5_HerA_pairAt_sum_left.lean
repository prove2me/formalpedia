-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_pairAt_sum_left
-- name    : Formalism.FourierDecayAlt.P5.HerA.pairAt_sum_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:41:24.872647+00:00
-- url     : https://prove2.me/theorems/e2f7de38-c338-458d-a561-95974e2c04f0
-- title:
--   Her A: pair At sum left
-- statement:
--   The Her A construction uses the pair At sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L112-L120

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

theorem Formalism.FourierDecayAlt.P5.HerA.pairAt_sum_left (hU : IntOn μ U) {c : Fin r → ℂ} (hc : c ∈ OmX r) {ι : Type} (s : Finset ι)
    (Φ : ι → RadSp k r z z' π π') (hΦ : ∀ i, Φ i ∈ U) {Ψ : RadSp k r z z' π π'} (hΨ : Ψ ∈ U) :
    pairAt μ (∑ i ∈ s, Φ i) Ψ c = ∑ i ∈ s, pairAt μ (Φ i) Ψ c := by sorry
