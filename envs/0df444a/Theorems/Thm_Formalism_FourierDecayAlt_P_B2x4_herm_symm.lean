-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_symm
-- name    : Formalism.FourierDecayAlt.P.B2x4.herm_symm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:26:29.242743+00:00
-- url     : https://prove2.me/theorems/26be60e2-3478-4886-bccf-2ebfe0588dc9
-- title:
--   B2x4: herm symm
-- statement:
--   The B2x4 construction uses the herm symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationInvarianceEverySetting.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationInvarianceEverySetting.lean#L45-L47

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

theorem Formalism.FourierDecayAlt.P.B2x4.herm_symm (hH : Hᴴ = H) (u w : Fin m → ℂ) : star (herm H u w) = herm H w u := by sorry
