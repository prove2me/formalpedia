-- Prove2me | Theorems.Thm_Formalism_REAL_fischerInner_oscillatorRaise
-- name    : Formalism.REAL.fischerInner_oscillatorRaise
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:28.770064+00:00
-- url     : https://prove2.me/theorems/75bfc0d7-b5e6-4784-a622-fab9e4711296
-- title:
--   REAL: fischer Inner oscillator Raise
-- statement:
--   The REAL construction uses the fischer Inner oscillator Raise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L125-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L125-L133

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
variable {M n' : ℕ}

theorem Formalism.REAL.fischerInner_oscillatorRaise (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n')
    (f g : MvPolynomial (Fin M × Fin n') ℂ) :
    fockF (bpl ε ε' i a f) g = (if sgnv ε ε' i a then 1 else -1) * fockF f (bop ε ε' i a g) := by sorry
