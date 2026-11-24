-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_right
-- name    : Formalism.FourierDecayAlt.P.B2x8.herm_smul_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:42:37.485804+00:00
-- url     : https://prove2.me/theorems/b508ec55-5188-440b-a4da-2e99c22c53fd
-- title:
--   B2x8: herm smul right
-- statement:
--   The B2x8 construction uses the herm smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L24-L25

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
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem Formalism.FourierDecayAlt.P.B2x8.herm_smul_right (c : ℂ) (u v : ι → ℂ) : herm H u (c • v) = conj c * herm H u v := by sorry
