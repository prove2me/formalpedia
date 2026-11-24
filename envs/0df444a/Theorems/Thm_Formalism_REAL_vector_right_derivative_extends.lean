-- Prove2me | Theorems.Thm_Formalism_REAL_vector_right_derivative_extends
-- name    : Formalism.REAL.vector_right_derivative_extends
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:49.126259+00:00
-- url     : https://prove2.me/theorems/ef5f3206-0d25-43b9-a46e-46e5fee5ef2c
-- title:
--   REAL: vector right derivative extends
-- statement:
--   The REAL construction uses the vector right derivative extends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/VectorComplexifiedDerivativeCommutator.lean#L14-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/VectorComplexifiedDerivativeCommutator.lean#L14-L32

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.REAL.vector_right_derivative_extends : RdExtV := by sorry
