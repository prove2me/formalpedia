-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_pair_measurable
-- name    : Formalism.FourierDecayAlt.P5.pair_measurable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:54:10.121182+00:00
-- url     : https://prove2.me/theorems/0d37017c-b569-5728-a9c2-252fd8e87c19
-- title:
--   P5: pair measurable
-- statement:
--   The P5 construction uses the pair measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableOfContinuousOnZero.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableOfContinuousOnZero.lean#L69-L82

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

theorem Formalism.FourierDecayAlt.P5.pair_measurable (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun q : Cf r 0 × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2))) := by sorry
