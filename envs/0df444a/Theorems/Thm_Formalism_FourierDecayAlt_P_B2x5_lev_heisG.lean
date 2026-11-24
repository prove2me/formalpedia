-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_heisG
-- name    : Formalism.FourierDecayAlt.P.B2x5.lev_heisG
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:58:18.960818+00:00
-- url     : https://prove2.me/theorems/7c5a5bd5-f2a3-4127-aff8-855ddf3ee740
-- title:
--   B2x5: lev heis G
-- statement:
--   The B2x5 construction uses the lev heis G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L587-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L587-L592

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.B2x5.lev_heisG (k r' : ℕ) {g : Mat k r'} (hg : g ∈ GV k r') (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) :
    ιLev k 1 r' g * heisG k r' (liftVec k 1 r' y) b = heisG k r' (liftVec k 1 r' (g *ᵥ y)) b * ιLev k 1 r' g := by sorry
