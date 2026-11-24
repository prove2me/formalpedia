-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_top_density_add_right
-- name    : Formalism.FourierDecayAlt.P5.top_density_add_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:43:29.766212+00:00
-- url     : https://prove2.me/theorems/c3a090ea-7a31-410f-8e64-c2974f24980e
-- title:
--   P5: top density add right
-- statement:
--   The P5 construction uses the top density add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L161-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L161-L164

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
  (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
  (w : List (Letter ℂ S))

theorem Formalism.FourierDecayAlt.P5.top_density_add_right (x y y' : Ix S → RadSp k r z z' π π') (a : ℂ) (c : Fin r → ℂ) (g : Mx k r) :
    topDens L st w x (y + a • y') c g = topDens L st w x y c g + conj a * topDens L st w x y' c g := by sorry
