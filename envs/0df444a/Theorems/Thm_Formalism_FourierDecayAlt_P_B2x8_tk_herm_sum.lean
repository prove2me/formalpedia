-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_tk_herm_sum
-- name    : Formalism.FourierDecayAlt.P.B2x8.tk_herm_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:59:45.995519+00:00
-- url     : https://prove2.me/theorems/b537d4ce-b0de-42ab-a64f-247613beceea
-- title:
--   B2x8: tk herm sum
-- statement:
--   The B2x8 construction uses the tk herm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L408-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L408-L413

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x8.tk_herm_sum {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u v : Fin m → ℂ) :
    ∑ j, herm H (bvec j) v * u j = herm H u v := by sorry
