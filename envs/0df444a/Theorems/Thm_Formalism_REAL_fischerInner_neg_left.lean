-- Prove2me | Theorems.Thm_Formalism_REAL_fischerInner_neg_left
-- name    : Formalism.REAL.fischerInner_neg_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:20:00.245896+00:00
-- url     : https://prove2.me/theorems/2cb2051f-d27a-4a92-97b9-0cfddb45f69a
-- title:
--   REAL: fischer Inner neg left
-- statement:
--   The REAL construction uses the fischer Inner neg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L52-L53

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

theorem Formalism.REAL.fischerInner_neg_left (f g : MvPolynomial σ ℂ) : fockF (-f) g = -fockF f g := by sorry
