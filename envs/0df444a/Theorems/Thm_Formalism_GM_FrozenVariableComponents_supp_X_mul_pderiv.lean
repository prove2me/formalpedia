-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_supp_X_mul_pderiv
-- name    : Formalism.GM.FrozenVariableComponents.supp_X_mul_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:25.760833+00:00
-- url     : https://prove2.me/theorems/655faae7-ebcb-4ff9-8d19-b5c2f7e2927d
-- title:
--   Frozen Variable Components: supp X mul pderiv
-- statement:
--   The Frozen Variable Components construction uses the supp X mul pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L398-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L398-L412

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

theorem Formalism.GM.FrozenVariableComponents.supp_X_mul_pderiv (a b : σ) (F : MvPolynomial σ K) (m : σ →₀ ℕ)
    (hm : m ∈ (X a * pderiv b F).support) :
    ∃ m0 ∈ F.support, ∀ x, x ≠ a → x ≠ b → m x = m0 x := by sorry
