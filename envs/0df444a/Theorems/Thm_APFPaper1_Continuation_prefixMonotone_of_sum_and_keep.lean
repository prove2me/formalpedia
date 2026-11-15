-- Prove2me | Theorems.Thm_APFPaper1_Continuation_prefixMonotone_of_sum_and_keep
-- name    : APFPaper1.Continuation.prefixMonotone_of_sum_and_keep
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:39:32.021314+00:00
-- url     : https://prove2.me/theorems/80ab7957-cd16-4549-ab71-248e4ca9046d
-- title:
--   SUM and KEEP imply prefix-monotone bills
-- statement:
--   Assume each whole-word bill is the finite sum of its kept nonnegative record costs and every appended fragment preserves those records. Every prefix bill is at most the whole-word bill.
--
--   The whole-word bill is calibration(resource(word)); SUM is a finite sum over kept records, not additivity over fragments or equality with the original A2 distinction-cost sum. The author ruling records readings, changes no FOUNDATION_INPUTS, and leaves the hypotheses in Lean. No physical realization or unconditional C1/C3/W-her is certified. KEEP and AFTER are quantified over all typed words/fragments, without an admitted-execution guard. The author call says admitted steps; the Lean hypothesis is stronger and stays explicit. AFTER is a structural record inclusion, stronger than the numerical bill inequality. CAPACITY is also separate and compares source to intermediate context budgets along every typed word. No Max or additive-fragment-load assumption is present.
-- source:
--   C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-14_session\astra\sib_v58_publication\source\Theorems\Thm_APFPaper1_Cont_prefix_from_sum_and_keep.lean:94

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

theorem APFPaper1.Continuation.prefixMonotone_of_sum_and_keep {Rec : Context → Type uK}
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (kept : (g : Context) → WordFrom Frag g → Finset (Rec g))
    (cost : (g : Context) → Rec g → NNReal)
    (hsum : ∀ (g : Context) (w : WordFrom Frag g),
      calibration g (resource g w) = ∑ r ∈ kept g w, cost g r)
    (hkeep : ∀ (g h k : Context) (w : Word Frag g h) (f : Frag h k),
      kept g ⟨h, w⟩ ⊆ kept g ⟨k, w.append (Word.single f)⟩) :
    PrefixMonotone resource calibration := by sorry
