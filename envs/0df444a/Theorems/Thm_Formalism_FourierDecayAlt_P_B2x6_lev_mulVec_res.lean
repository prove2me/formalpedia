-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mulVec_res
-- name    : Formalism.FourierDecayAlt.P.B2x6.lev_mulVec_res
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:04:57.072822+00:00
-- url     : https://prove2.me/theorems/fa767c54-f433-46fa-a97a-df9f54d840f4
-- title:
--   B2x6: lev mul Vec res
-- statement:
--   The B2x6 construction uses the lev mul Vec res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentHeisenbergDecomposition.lean#L210-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentHeisenbergDecomposition.lean#L210-L215

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x6.lev_mulVec_res (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    res (ιLev k 1 r' g *ᵥ u) = g *ᵥ res u := by sorry
