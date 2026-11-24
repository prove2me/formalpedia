-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NU_sub_sub
-- name    : Formalism.NormUnitaryCountingLemmas.NU.sub_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:18:06.633553+00:00
-- url     : https://prove2.me/theorems/f94d5f1a-57bb-4ae6-be47-e3a152cea58a
-- title:
--   NU: sub sub
-- statement:
--   The NU construction uses the sub sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormUnitary.lean#L97-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormUnitary.lean#L97-L111

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.NU
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem Formalism.NormUnitaryCountingLemmas.NU.sub_sub (V : Matrix σ σ ℂ) (hV : V * star V = 1) (F : MvPolynomial σ ℂ) :
    sub (star V) (sub V F) = F := by sorry
