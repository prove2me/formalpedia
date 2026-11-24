-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_op_local
-- name    : Formalism.FourierDecayAlt.P.PositiveOrbitOpen.op_local
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:55.836542+00:00
-- url     : https://prove2.me/theorems/a64bf637-1696-4e2d-8922-bf92f9f7bc93
-- title:
--   Positive Orbit Open: op local
-- statement:
--   The Positive Orbit Open construction uses the op local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveOrbitOpen.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveOrbitOpen.lean#L63-L69

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveOrbitOpen
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.PositiveOrbitOpen.op_local (Θ : DiffOp k r Wp Wq) {f₁ f₂ : Mat k r → (Wq →L[ℂ] Wp)} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) : ∀ x ∈ V, x ∈ GV k r → opApply Θ f₁ x = opApply Θ f₂ x := by sorry
