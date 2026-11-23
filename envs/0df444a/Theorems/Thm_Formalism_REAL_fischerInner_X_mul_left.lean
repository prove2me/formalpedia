-- Prove2me | Theorems.Thm_Formalism_REAL_fischerInner_X_mul_left
-- name    : Formalism.REAL.fischerInner_X_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:55:32.731421+00:00
-- url     : https://prove2.me/theorems/03adacb7-8eb1-488c-a960-38937e6b860e
-- title:
--   REAL: fischer Inner X mul left
-- statement:
--   The REAL construction uses the fischer Inner X mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L107-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L107-L109

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

theorem Formalism.REAL.fischerInner_X_mul_left [DecidableEq σ] (v : σ) (f g : MvPolynomial σ ℂ) :
    fockF (X v * f) g = fockF f (pderiv v g) := by sorry
