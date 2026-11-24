-- Prove2me | Theorems.Thm_Formalism_REAL_tendsto_slope_mul_exp_smul
-- name    : Formalism.REAL.tendsto_slope_mul_exp_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:55.98604+00:00
-- url     : https://prove2.me/theorems/07b17ae8-8740-4191-8300-7e8758dd8f60
-- title:
--   REAL: tendsto slope mul exp smul
-- statement:
--   The REAL construction uses the tendsto slope mul exp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CartanInvolutionConjTransposeMul.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CartanInvolutionConjTransposeMul.lean#L30-L34

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

theorem Formalism.REAL.tendsto_slope_mul_exp_smul {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 (g * X)) := by sorry
