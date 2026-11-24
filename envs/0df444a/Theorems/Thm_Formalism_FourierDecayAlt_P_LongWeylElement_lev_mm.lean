-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mm
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.lev_mm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:08:17.09926+00:00
-- url     : https://prove2.me/theorems/afeb22b7-92ef-4d0c-a97e-1aa066004276
-- title:
--   Long Weyl Element: lev mm
-- statement:
--   The Long Weyl Element construction uses the lev mm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L55-L61

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mm

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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement

theorem Formalism.FourierDecayAlt.P.LongWeylElement.lev_mm (k r' : ℕ) (g : Mat k r') (s t : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' s) (levPos k 1 r' t) = g s t := by sorry
