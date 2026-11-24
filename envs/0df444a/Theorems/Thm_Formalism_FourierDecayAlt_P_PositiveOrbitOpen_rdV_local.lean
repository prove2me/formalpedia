-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_rdV_local
-- name    : Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rdV_local
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:42.396921+00:00
-- url     : https://prove2.me/theorems/c82e1d0d-db4b-4d42-b357-c2bb46dcaa95
-- title:
--   Positive Orbit Open: rd V local
-- statement:
--   The Positive Orbit Open construction uses the rd V local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveOrbitOpen.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveOrbitOpen.lean#L25-L37

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rdV_local {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) {X : Mat k r} (hX : inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → RdV X f₁ x = RdV X f₂ x := by sorry
