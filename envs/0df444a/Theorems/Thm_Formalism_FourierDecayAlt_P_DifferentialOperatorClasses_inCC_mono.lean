-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_inCC_mono
-- name    : Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.inCC_mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:32:49.116141+00:00
-- url     : https://prove2.me/theorems/48cd4859-3c47-4f26-85c4-a00d73cf4e60
-- title:
--   Differential Operator Classes: in CC mono
-- statement:
--   The Differential Operator Classes construction uses the in CC mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean#L75-L78

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

theorem Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.inCC_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m m' : ℕ} (hm : m' ≤ m)
    {F : B.Mat k r → E} (hF : B.InCC A m F) : B.InCC A m' F := by sorry
