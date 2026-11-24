-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_eq_frob
-- name    : Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_eq_frob
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:22.267597+00:00
-- url     : https://prove2.me/theorems/26934e1c-97b1-4dd9-872a-1fcae61ec8a1
-- title:
--   Beta Sesquilinearity: g N eq frob
-- statement:
--   The Beta Sesquilinearity construction uses the g N eq frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L265-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean#L265-L268

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing

theorem Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_eq_frob {k r : ℕ} (g : Mat k r) : gN g = ‖g‖ := by sorry
