-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_hasDerivAt
-- name    : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_hasDerivAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:29:16.363804+00:00
-- url     : https://prove2.me/theorems/c58a1670-b85d-4e59-8c7c-9595cd8709e8
-- title:
--   Capelli Word Sum Expansion: loc has Deriv At
-- statement:
--   The Capelli Word Sum Expansion construction uses the loc has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L31-L45

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

theorem Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_hasDerivAt {m : ℕ∞} (hm : 1 ≤ m) {f : Mat k r → E} {g X : Mat k r} (h : Loc m f g)
    (hg : g ∈ GV k r) (hX : inLie k r X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (RdV X f g) 0 := by sorry
