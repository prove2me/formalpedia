-- Prove2me | Theorems.Thm_Formalism_REAL_fischerInner_neg_right
-- name    : Formalism.REAL.fischerInner_neg_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:21:49.478231+00:00
-- url     : https://prove2.me/theorems/803e8736-f550-48df-a963-91979d31fe89
-- title:
--   REAL: fischer Inner neg right
-- statement:
--   The REAL construction uses the fischer Inner neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L55-L56

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

theorem Formalism.REAL.fischerInner_neg_right (f g : MvPolynomial σ ℂ) : fockF f (-g) = -fockF f g := by sorry
