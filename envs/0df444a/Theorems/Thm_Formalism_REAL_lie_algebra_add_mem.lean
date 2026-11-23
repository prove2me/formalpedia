-- Prove2me | Theorems.Thm_Formalism_REAL_lie_algebra_add_mem
-- name    : Formalism.REAL.lie_algebra_add_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:33.522804+00:00
-- url     : https://prove2.me/theorems/f40592c4-26db-4ed2-ac85-3fb089271758
-- title:
--   REAL: lie algebra add mem
-- statement:
--   The REAL construction uses the lie algebra add mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CartanInvolutionConjTransposeMul.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CartanInvolutionConjTransposeMul.lean#L49-L52

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

theorem Formalism.REAL.lie_algebra_add_mem {n : ℕ} (ε : Fin n → Bool) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hY : inG ε Y) : inG ε (X + Y) := by sorry
