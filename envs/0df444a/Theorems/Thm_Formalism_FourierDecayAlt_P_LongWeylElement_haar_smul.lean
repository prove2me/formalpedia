-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_haar_smul
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.haar_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:03:10.163216+00:00
-- url     : https://prove2.me/theorems/ccc0a2a0-d2fe-409d-a582-679aa1164fd9
-- title:
--   Long Weyl Element: haar smul
-- statement:
--   The Long Weyl Element construction uses the haar smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L957-L963
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L957-L963

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

theorem Formalism.FourierDecayAlt.P.LongWeylElement.haar_smul (HU : HaarUnique) {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn U μ) (hν : IsHaarOn U ν) : ∃ a : ℝ≥0, 0 < a ∧ ν = a • μ := by sorry
