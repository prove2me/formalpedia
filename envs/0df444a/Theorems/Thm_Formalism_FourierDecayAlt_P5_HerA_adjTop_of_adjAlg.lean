-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_adjTop_of_adjAlg
-- name    : Formalism.FourierDecayAlt.P5.HerA.adjTop_of_adjAlg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:40:33.809902+00:00
-- url     : https://prove2.me/theorems/915aacdf-c094-445d-b9cd-bf8214ece6c1
-- title:
--   Her A: adj Top of adj Alg
-- statement:
--   The Her A construction uses the adj Top of adj Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L213-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L213-L236

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P5.HerA.adjTop_of_adjAlg (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (U : Submodule ℂ (RadSp P.k P.r z z' π π')) (hU : IntOn μ U) (hK : K (Fin.last P.r) ≤ U)
    (hF : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ e e',
      (Fr.ofWord L st w).F e e' ∈ adjAlg μ U hU ∧ (Fr.ofWord L st w).d L e e' ∈ adjAlg μ U hU) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by sorry
