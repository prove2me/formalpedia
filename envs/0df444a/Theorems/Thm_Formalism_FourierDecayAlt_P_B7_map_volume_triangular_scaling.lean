-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B7_map_volume_triangular_scaling
-- name    : Formalism.FourierDecayAlt.P.B7.map_volume_triangular_scaling
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:06:05.789553+00:00
-- url     : https://prove2.me/theorems/3dbd1d69-5c9e-400e-9453-fc4ae40126b1
-- title:
--   B7: map volume triangular scaling
-- statement:
--   The B7 construction uses the map volume triangular scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L678-L685
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralAeConvergenceContinuity.lean#L678-L685

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.B7.map_volume_triangular_scaling (s : ℝ) (hs : 0 < s) :
    (volume : Measure (Fin r → ℂ)).map (fun c a => ((s ^ (r - a.val) : ℝ) : ℂ) * c a) =
      (∏ a : Fin r, Real.toNNReal (((s ^ (r - a.val)) ^ 2)⁻¹)) • (volume : Measure (Fin r → ℂ)) := by sorry
