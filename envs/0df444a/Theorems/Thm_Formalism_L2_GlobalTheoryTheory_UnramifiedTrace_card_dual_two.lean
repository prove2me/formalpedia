-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_UnramifiedTrace_card_dual_two
-- name    : Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_dual_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:12.132494+00:00
-- url     : https://prove2.me/theorems/ac24a8cf-8bfe-4a36-8d7b-23a7e0ecdc86
-- title:
--   Unramified Trace: card dual two
-- statement:
--   The Unramified Trace construction uses the card dual two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean#L74-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean#L74-L120

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_UnramifiedTrace_CardFilterSubtype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
variable {K X : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [Fintype (Module.Dual K X)]

theorem Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_dual_two (te x : X) (hte : te ≠ 0) (hx : x ∉ Submodule.span K {te}) :
    (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card =
      Fintype.card K ^ (Module.finrank K X - 2) := by sorry
