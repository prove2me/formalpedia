-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_fixes_isotropic_vector
-- name    : Formalism.FourierDecayAlt.P.B2x8.heisenberg_fixes_isotropic_vector
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:01:20.435131+00:00
-- url     : https://prove2.me/theorems/f9bb33c9-3bba-47f9-936a-9e94baceca3e
-- title:
--   B2x8: heisenberg fixes isotropic vector
-- statement:
--   The B2x8 construction uses the heisenberg fixes isotropic vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L953-L955
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L953-L955

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

theorem Formalism.FourierDecayAlt.P.B2x8.heisenberg_fixes_isotropic_vector (x : HPar k r') : heis0 k r' x *ᵥ e0 k r' = e0 k r' := by sorry
