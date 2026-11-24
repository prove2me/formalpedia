-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_pairAt_snd_left
-- name    : Formalism.FourierDecayAlt.P5.HerA.pairAt_snd_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:41:13.247859+00:00
-- url     : https://prove2.me/theorems/6c6bf6d9-86b7-483e-b473-8782b94367d0
-- title:
--   Her A: pair At snd left
-- statement:
--   The Her A construction uses the pair At snd left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L170-L175

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

theorem Formalism.FourierDecayAlt.P5.HerA.pairAt_snd_left {hU : IntOn μ U} {a : Pr (RadSp k r z z' π π')} (ha : a ∈ adjAlg μ U hU) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {Φ Ψ : RadSp k r z z' π π'} (hΦ : Φ ∈ U) (hΨ : Ψ ∈ U) :
    pairAt μ (a.2.unop Φ) Ψ c = pairAt μ Φ (a.1 Ψ) c := by sorry
