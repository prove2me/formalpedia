-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_heisG_comm
-- name    : Formalism.FourierDecayAlt.P.B2x7.heisG_comm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:58:17.105038+00:00
-- url     : https://prove2.me/theorems/170523fd-96ff-4c7a-9b66-ef593b366643
-- title:
--   B2x7: heis G comm
-- statement:
--   The B2x7 construction uses the heis G comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean#L130-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean#L130-L145

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x7.heisG_comm (g : Mat k (1 + r')) (hg : g ∈ GV k (1 + r')) (c : ℝ) (hc : g *ᵥ e0 k r' = (c : ℂ) • e0 k r')
    (v : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    g * heisG k r' v b = heisG k r' ((c : ℂ) • (g *ᵥ v)) ((c : ℂ) ^ 2 * b) * g := by sorry
