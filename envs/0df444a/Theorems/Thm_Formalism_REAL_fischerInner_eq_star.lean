-- Prove2me | Theorems.Thm_Formalism_REAL_fischerInner_eq_star
-- name    : Formalism.REAL.fischerInner_eq_star
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:19:59.628863+00:00
-- url     : https://prove2.me/theorems/a311522b-2330-4c37-b58d-b729f1eec74b
-- title:
--   REAL: fischer Inner eq star
-- statement:
--   The REAL construction uses the fischer Inner eq star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L58-L63

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

theorem Formalism.REAL.fischerInner_eq_star (f g : MvPolynomial σ ℂ) : fockF f g = star (fockF g f) := by sorry
