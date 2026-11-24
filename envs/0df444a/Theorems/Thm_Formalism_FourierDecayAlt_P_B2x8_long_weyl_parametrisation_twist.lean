-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_long_weyl_parametrisation_twist
-- name    : Formalism.FourierDecayAlt.P.B2x8.long_weyl_parametrisation_twist
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:00:09.295813+00:00
-- url     : https://prove2.me/theorems/c2c68702-5262-484f-b4bb-d6d2d8bb50fb
-- title:
--   B2x8: long weyl parametrisation twist
-- statement:
--   The B2x8 construction uses the long weyl parametrisation twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1222-L1232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1222-L1232

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

theorem Formalism.FourierDecayAlt.P.B2x8.long_weyl_parametrisation_twist (c₀ : ℂ) (hc : c₀ ≠ 0) (p : ℂ × HPar k r') (h1 : p.1 ≠ 0) (h2 : p.2.2 ≠ 0) :
    w0 k r' c₀ *ᵥ Ψt k r' p = Ψt k r' (Tw k r' c₀ p) := by sorry
