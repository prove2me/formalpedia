-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_sgs_GV
-- name    : Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:20:47.416079+00:00
-- url     : https://prove2.me/theorems/94e524b9-3c62-4651-9a99-2deffcb1aa45
-- title:
--   Positive Orbit Open: sgs GV
-- statement:
--   The Positive Orbit Open construction uses the sgs GV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveOrbitOpen.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositiveOrbitOpen.lean#L123-L126

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
omit [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {y : Mat k r} (hy : y ∈ GV k r) :
    sgs p y ∈ GV k r := by sorry
