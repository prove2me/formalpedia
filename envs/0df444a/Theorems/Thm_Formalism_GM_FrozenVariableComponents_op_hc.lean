-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_op_hc
-- name    : Formalism.GM.FrozenVariableComponents.op_hc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:30.041262+00:00
-- url     : https://prove2.me/theorems/d6606dab-66ac-4750-a92f-4696c98d454d
-- title:
--   Frozen Variable Components: op hc
-- statement:
--   The Frozen Variable Components construction uses the op hc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L461-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L461-L481

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable {K : Type*} [CommRing K] {σ : Type*}

theorem Formalism.GM.FrozenVariableComponents.op_hc (x y : σ) (t : ℕ) (F : MvPolynomial σ K) :
    homogeneousComponent t (X x * pderiv y F) = X x * pderiv y (homogeneousComponent t F) := by sorry
