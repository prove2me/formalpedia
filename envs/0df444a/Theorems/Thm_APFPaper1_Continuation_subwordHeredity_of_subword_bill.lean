-- Prove2me | Theorems.Thm_APFPaper1_Continuation_subwordHeredity_of_subword_bill
-- name    : APFPaper1.Continuation.subwordHeredity_of_subword_bill
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:40:22.211877+00:00
-- url     : https://prove2.me/theorems/34489825-aa98-4886-86db-a33f68622579
-- title:
--   Subword bill comparison and CAPACITY give W-her
-- statement:
--   If every middle subword bills no more than its composite and capacities do not decrease along typed words, every middle subword of a Cont word is itself in Cont from an intermediate raw input.
--
--   The whole-word bill is calibration(resource(word)); SUM is a finite sum over kept records, not additivity over fragments or equality with the original A2 distinction-cost sum. The author ruling records readings, changes no FOUNDATION_INPUTS, and leaves the hypotheses in Lean. No physical realization or unconditional C1/C3/W-her is certified. KEEP and AFTER are quantified over all typed words/fragments, without an admitted-execution guard. The author call says admitted steps; the Lean hypothesis is stronger and stays explicit. AFTER is a structural record inclusion, stronger than the numerical bill inequality. CAPACITY is also separate and compares source to intermediate context budgets along every typed word. No Max or additive-fragment-load assumption is present.
-- source:
--   C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-14_session\astra\sib_v58_publication\source\Theorems\Thm_APFPaper1_Cont_prefix_from_sum_and_keep.lean:159

import Definitions.Def_APFPaper1_ContextualEquivalence
import Theorems.Thm_APFPaper1_Continuation_cont_prefix
import Theorems.Thm_APFPaper1_Continuation_contHereditary_iff_cont
import Theorems.Thm_APFPaper1_Continuation_prefix_closed_iff_hereditary
import Theorems.Thm_APFPaper1_Continuation_prefixMonotone_of_resource_mono
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
namespace APFPaper1.Continuation
end APFPaper1.Continuation
open APFPaper1.Continuation
universe uC uF uX uR uK
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}











/-! ### Contiguous subwords -/

theorem APFPaper1.Continuation.subwordHeredity_of_subword_bill
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (hsub : ∀ (g a b c : Context) (A : Word Frag g a) (M : Word Frag a b) (B : Word Frag b c),
      calibration a (resource a ⟨b, M⟩) ≤ calibration g (resource g (sandwich A M B)))
    (hcap : ∀ (g a : Context), Word Frag g a → C g ≤ C a) :
    SubwordHeredity (Cont step resource calibration C)
      (fun g h M => ∃ x : Raw g, Cont step resource calibration C g x ⟨h, M⟩) := by sorry
