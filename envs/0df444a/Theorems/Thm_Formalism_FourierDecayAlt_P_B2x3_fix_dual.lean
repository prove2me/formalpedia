-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_fix_dual
-- name    : Formalism.FourierDecayAlt.P.B2x3.fix_dual
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:53:44.553931+00:00
-- url     : https://prove2.me/theorems/e4be9d77-743e-487b-937c-dbc44913e65c
-- title:
--   B2x3: fix dual
-- statement:
--   The B2x3 construction uses the fix dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L542-L547
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L542-L547

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x3.fix_dual {g : Mat k r} (hg : g ∈ GV k r) {f : Fin (2 * r + k + 1) → ℂ} (hf : g *ᵥ f = f) :
    gᴴ *ᵥ (Hpk k r *ᵥ f) = Hpk k r *ᵥ f := by sorry
