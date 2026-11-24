-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_herm_smul_left
-- name    : Formalism.FourierDecayAlt.P.B2x7.herm_smul_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:20:24.402704+00:00
-- url     : https://prove2.me/theorems/e61a8d7b-c05d-4919-8d4c-bba8c15015d2
-- title:
--   B2x7: herm smul left
-- statement:
--   The B2x7 construction uses the herm smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean#L99-L102

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_herm_smul_left

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

theorem Formalism.FourierDecayAlt.P.B2x7.herm_smul_left {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (x w : ι → ℂ) :
    herm H (c • x) w = c * herm H x w := by sorry
