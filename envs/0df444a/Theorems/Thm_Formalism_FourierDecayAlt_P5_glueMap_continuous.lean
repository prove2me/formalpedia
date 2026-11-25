-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_glueMap_continuous
-- name    : Formalism.FourierDecayAlt.P5.glueMap_continuous
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:56:32.724418+00:00
-- url     : https://prove2.me/theorems/f97d094f-2dee-499e-b188-0a9afb778dec
-- title:
--   P5: glue Map continuous
-- statement:
--   The P5 construction uses the glue Map continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableOfContinuousOnZero.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableOfContinuousOnZero.lean#L48-L56

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableOfContinuousOnZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem Formalism.FourierDecayAlt.P5.glueMap_continuous (c : Fin r → ℂ) : Continuous (glueMap (k := k) c) := by sorry
