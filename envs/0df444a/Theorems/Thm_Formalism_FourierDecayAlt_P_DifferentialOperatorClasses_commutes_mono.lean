-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_commutes_mono
-- name    : Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.commutes_mono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:13:26.398836+00:00
-- url     : https://prove2.me/theorems/936ff25f-be5f-4130-a013-a9b3ef8c17b0
-- title:
--   Differential Operator Classes: commutes mono
-- statement:
--   The Differential Operator Classes construction uses the commutes mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean#L71-L73

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.commutes_mono (D : B.RealPlaceData k r Wp Wq) {U V : Set (B.Mat k r)} (hUV : U ⊆ V)
    {Θ : B.DiffOp k r Wp Wq} (h : B.Commutes D V Θ) : B.Commutes D U Θ := by sorry
