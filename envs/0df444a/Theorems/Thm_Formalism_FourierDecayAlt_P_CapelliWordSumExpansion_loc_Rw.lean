-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_Rw
-- name    : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_Rw
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:14:04.166882+00:00
-- url     : https://prove2.me/theorems/0dc07762-6ff4-493a-88d4-93685efec968
-- title:
--   Capelli Word Sum Expansion: loc Rw
-- statement:
--   The Capelli Word Sum Expansion construction uses the loc Rw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L58-L68

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

theorem Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_Rw {N : ℕ} {f : Mat k r → E} {g : Mat k r} (h : Loc (N : ℕ∞) f g) (w : List (Mat k r))
    (hw : ∀ X ∈ w, inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) : Loc (m : ℕ∞) (Rw w f) g := by sorry
