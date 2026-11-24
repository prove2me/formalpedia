-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_coordinate_split_assoc_measurePreserving
-- name    : Formalism.FourierDecayAlt.P5.coordinate_split_assoc_measurePreserving
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:39:55.061252+00:00
-- url     : https://prove2.me/theorems/4fe47af5-52c4-4fa8-aa86-8b2cbd518dd1
-- title:
--   P5: coordinate split assoc measure Preserving
-- statement:
--   The P5 construction uses the coordinate split assoc measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSplitAssocMeasurePreserving.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSplitAssocMeasurePreserving.lean#L76-L81

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

theorem Formalism.FourierDecayAlt.P5.coordinate_split_assoc_measurePreserving (l : Fin r) {β : Type} [MeasurableSpace β] (ν : Measure β) [SFinite ν] :
    MeasurePreserving (coordinateSplitAssoc l (β := β)) (volume.prod ν) (volume.prod (volume.prod ν)) := by sorry
