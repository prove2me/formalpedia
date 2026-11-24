-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_level_product_eq_list_prod
-- name    : Formalism.FourierDecayAlt.P5.level_product_eq_list_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:42:46.429657+00:00
-- url     : https://prove2.me/theorems/66e80d6a-5772-4ce0-9a60-c3371f4f14d6
-- title:
--   P5: level product eq list prod
-- statement:
--   The P5 construction uses the level product eq list prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSplitAssocMeasurePreserving.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSplitAssocMeasurePreserving.lean#L32-L45

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P5.level_product_eq_list_prod (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) (n : ℕ) :
    ∀ i, r - i = n → i ≤ r →
    levelProduct L w i = ((List.range' i n).reverse.map fun j => if h : j < r then bTl L ⟨j, h⟩ w else 1).prod := by sorry
