-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_nuN_eq
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.nuN_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:18.209443+00:00
-- url     : https://prove2.me/theorems/b69c2fce-cf20-4d20-b17a-39649cb66cd5
-- title:
--   Long Weyl Element: nu N eq
-- statement:
--   The Long Weyl Element construction uses the nu N eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L853-L880
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L853-L880

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
attribute [local instance] sfHeis

theorem Formalism.FourierDecayAlt.P.LongWeylElement.nuN_eq (hC : HeisConjLevMeas) (hN : ClosedN) (μ' : Measure (Mt k r')) (hμ' : IsHaarOn (Nset k r') μ') :
    ((μHeis k r').prod (μ'.map (levM k r'))).map mulM =
      ((volume : Measure (HPar k r')).prod μ').map (thetaF k r') := by sorry
