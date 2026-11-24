-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerA_form_last
-- name    : Formalism.FourierDecayAlt.P5.HerA.form_last
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:40:52.763866+00:00
-- url     : https://prove2.me/theorems/4f35f388-b9ab-494b-ada5-dbbc1c076022
-- title:
--   Her A: form last
-- statement:
--   The Her A construction uses the form last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumPairAtStarMul.lean#L20-L32

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

theorem Formalism.FourierDecayAlt.P5.HerA.form_last (μ : Measure (Mt k r)) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ (Fin.last r) x y c = ∑ a, pairAt μ (x a) (y a) c := by sorry
