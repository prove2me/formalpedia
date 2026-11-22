-- Prove2me | Theorems.Thm_Formalism_REAL_fischerInner_monomial_left
-- name    : Formalism.REAL.fischerInner_monomial_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:22.543565+00:00
-- url     : https://prove2.me/theorems/0df060dd-41e2-4f43-86e8-6576904e7534
-- title:
--   REAL: fischer Inner monomial left
-- statement:
--   The REAL construction uses the fischer Inner monomial left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L65-L69

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

theorem Formalism.REAL.fischerInner_monomial_left (u : σ →₀ ℕ) (c : ℂ) (g : MvPolynomial σ ℂ) :
    fockF (monomial u c) g = c * star (g.coeff u) * ((∏ k ∈ u.support, (u k).factorial : ℕ) : ℂ) := by sorry
