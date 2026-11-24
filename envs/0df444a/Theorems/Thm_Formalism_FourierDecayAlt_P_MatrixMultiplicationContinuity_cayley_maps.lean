-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_cayley_maps
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:49:30.268346+00:00
-- url     : https://prove2.me/theorems/80628ae6-dbf4-4808-9bf4-93002d7dc9cf
-- title:
--   Matrix Multiplication Continuity: cayley maps
-- statement:
--   The Matrix Multiplication Continuity construction uses the cayley maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L258-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L258-L274

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps {ε : Fin (2 * r + k + 1) → Bool} {P : Formalism.FourierDecayAlt.ThreeDimData.Mx k r}
    (hP : PI.UpqRep.IsCayleyU k r ε P) :
    Set.MapsTo (fun g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r => P * g * P⁻¹) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
      (PI.UpqRep.UJset ε) := by sorry
