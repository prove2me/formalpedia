-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_os_cell
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.os_cell
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:25.971797+00:00
-- url     : https://prove2.me/theorems/80418fd5-cdae-499e-a4e9-5bddabcd346b
-- title:
--   Long Weyl Element: os cell
-- statement:
--   The Long Weyl Element construction uses the os cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L822-L830
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L822-L830

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
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
variable {k r r' : ℕ}

theorem Formalism.FourierDecayAlt.P.LongWeylElement.os_cell (x x' : HPar k r') (c : ℂ) (B n n' m : Mat k r') (hn : IsUnit n.det) :
    oneStep k r' x c (n⁻¹ * B * m * n') x' =
      (ιLev k 1 r' n * heis0 k r' x)⁻¹ * (w0 k r' c * ιLev k 1 r' B) * ιLev k 1 r' m *
        (ιLev k 1 r' n' * heis0 k r' x') := by sorry
