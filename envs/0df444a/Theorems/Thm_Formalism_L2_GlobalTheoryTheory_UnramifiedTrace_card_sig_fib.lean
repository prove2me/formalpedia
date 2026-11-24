-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_UnramifiedTrace_card_sig_fib
-- name    : Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_sig_fib
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:20.018174+00:00
-- url     : https://prove2.me/theorems/493d9daf-ecf3-467e-bd6b-0ed7d53282ac
-- title:
--   Unramified Trace: card sig fib
-- statement:
--   The Unramified Trace construction uses the card sig fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean#L131-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean#L131-L149

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

theorem Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_sig_fib {A : Type*} {B : A → Type*} [Fintype A] [∀ a, Fintype (B a)] {Y : Type*} [DecidableEq Y]
    (ι : ∀ a, B a → Y) (P : A → Y → Prop) [∀ a y, Decidable (P a y)] (hι : ∀ a b, P a (ι a b)) (hu : ∀ a y, P a y → ∃! b, ι a b = y) (y : Y) :
    (Finset.univ.filter (fun p : (Σ a, B a) => ι p.1 p.2 = y)).card = (Finset.univ.filter (fun a => P a y)).card := by sorry
