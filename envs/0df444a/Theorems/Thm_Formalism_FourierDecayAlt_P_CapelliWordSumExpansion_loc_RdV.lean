-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_RdV
-- name    : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_RdV
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:29:07.642034+00:00
-- url     : https://prove2.me/theorems/5970f6bc-277f-4a43-b56a-ba2ae2dc804a
-- title:
--   Capelli Word Sum Expansion: loc Rd V
-- statement:
--   The Capelli Word Sum Expansion construction uses the loc Rd V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L47-L56

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_RdV {m : ℕ∞} {f : Mat k r → E} {g X : Mat k r} (hX : inLie k r X) (h : Loc (m + 1) f g) :
    Loc m (RdV X f) g := by sorry
