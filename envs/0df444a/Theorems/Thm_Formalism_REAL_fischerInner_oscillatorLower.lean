-- Prove2me | Theorems.Thm_Formalism_REAL_fischerInner_oscillatorLower
-- name    : Formalism.REAL.fischerInner_oscillatorLower
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:22.782872+00:00
-- url     : https://prove2.me/theorems/450df52e-3cb5-434a-a4fd-b7ae1a6379d8
-- title:
--   REAL: fischer Inner oscillator Lower
-- statement:
--   The REAL construction uses the fischer Inner oscillator Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L115-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ProdFactorialSupportSubSingle.lean#L115-L123

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

theorem Formalism.REAL.fischerInner_oscillatorLower (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n')
    (f g : MvPolynomial (Fin M × Fin n') ℂ) :
    fockF (bop ε ε' i a f) g = (if sgnv ε ε' i a then 1 else -1) * fockF f (bpl ε ε' i a g) := by sorry
