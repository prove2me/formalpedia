-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DifferentialOperatorClasses_rw_zero
-- name    : Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.rw_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:12:24.093365+00:00
-- url     : https://prove2.me/theorems/c43f391a-a66b-4a53-be8e-5c27635731cf
-- title:
--   Differential Operator Classes: rw zero
-- statement:
--   The Differential Operator Classes construction uses the rw zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean#L95-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellVanishingOfCommute.lean#L95-L119

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

theorem Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.rw_zero (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (G : B.Mat k r → (Wq →L[ℂ] Wp))
    (hG : ∀ g ∈ B.GV k r, G g ≠ 0 → ε ≤ Gf k r D.z D.z' g) :
    ∀ v : List (B.Mat k r), (∀ X ∈ v, B.inLie k r X) →
      ∀ g ∈ B.GV k r, Gf k r D.z D.z' g < ε → B.Rw v G g = 0 := by sorry
