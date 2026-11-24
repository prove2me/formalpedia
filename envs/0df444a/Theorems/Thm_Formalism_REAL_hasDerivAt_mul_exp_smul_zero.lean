-- Prove2me | Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero
-- name    : Formalism.REAL.hasDerivAt_mul_exp_smul_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:42:42.806318+00:00
-- url     : https://prove2.me/theorems/a9f858a7-65ef-47e7-8732-df70301fc5d5
-- title:
--   REAL: has Deriv At mul exp smul zero
-- statement:
--   The REAL construction uses the has Deriv At mul exp smul zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CartanInvolutionConjTransposeMul.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CartanInvolutionConjTransposeMul.lean#L38-L40

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
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

theorem Formalism.REAL.hasDerivAt_mul_exp_smul_zero {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by sorry
