-- Prove2me | Theorems.Thm_Formalism_REAL_prod_factorial_support_sub_single
-- name    : Formalism.REAL.prod_factorial_support_sub_single
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:49.277338+00:00
-- url     : https://prove2.me/theorems/e931fa0c-b15d-457c-b318-525ff5908e5f
-- title:
--   REAL: prod factorial support sub single
-- statement:
--   The REAL construction uses the prod factorial support sub single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L71-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L71-L92

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {σ : Type*}

theorem Formalism.REAL.prod_factorial_support_sub_single [DecidableEq σ] (u : σ →₀ ℕ) (v : σ) (hv : u v ≠ 0) :
    (∏ k ∈ u.support, (u k).factorial) =
      u v * ∏ k ∈ (u - Finsupp.single v 1 : σ →₀ ℕ).support, ((u - Finsupp.single v 1 : σ →₀ ℕ) k).factorial := by sorry
