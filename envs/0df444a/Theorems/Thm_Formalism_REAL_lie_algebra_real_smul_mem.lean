-- Prove2me | Theorems.Thm_Formalism_REAL_lie_algebra_real_smul_mem
-- name    : Formalism.REAL.lie_algebra_real_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:51.443276+00:00
-- url     : https://prove2.me/theorems/499e7143-841c-4b6c-9b98-95bbd4e53257
-- title:
--   REAL: lie algebra real smul mem
-- statement:
--   The REAL construction uses the lie algebra real smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CartanInvolutionConjTransposeMul.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CartanInvolutionConjTransposeMul.lean#L54-L58

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

theorem Formalism.REAL.lie_algebra_real_smul_mem {n : ℕ} (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (r : ℝ) : inG ε ((r : ℂ) • X) := by sorry
