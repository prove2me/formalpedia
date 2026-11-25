-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_expand_words
-- name    : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:49:28.316013+00:00
-- url     : https://prove2.me/theorems/b01bcf33-3d7d-4726-a765-a7135f7f55c3
-- title:
--   Capelli Word Sum Expansion: expand words
-- statement:
--   The Capelli Word Sum Expansion construction uses the expand words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L153-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L153-L178

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

theorem Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ cw ∈ expand k r ts, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ ts.length := by sorry
