-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_level_integrand_split_point
-- name    : Formalism.FourierDecayAlt.P5.level_integrand_split_point
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:43:32.757489+00:00
-- url     : https://prove2.me/theorems/d851d6ae-fe85-43b7-9d4a-6c44bf00e004
-- title:
--   P5: level integrand split point
-- statement:
--   The P5 construction uses the level integrand split point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSplitAssocMeasurePreserving.lean#L83-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSplitAssocMeasurePreserving.lean#L83-L95

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

theorem Formalism.FourierDecayAlt.P5.level_integrand_split_point (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (w : List (Letter ℂ S)) (l : Fin r) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ)
    (q : Cf r l.succ × Mt k r) :
    levelIntegrand L st w l.castSucc x y c ((coordinateSplitAssoc l).symm (t, q)) =
      ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * levelIntegrand L st w l.succ (act (bTl L l w) x) (act (bTl L l w) y)
        (Function.update c l t) q := by sorry
