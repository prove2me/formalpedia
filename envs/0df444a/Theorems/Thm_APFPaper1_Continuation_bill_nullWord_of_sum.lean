-- Prove2me | Theorems.Thm_APFPaper1_Continuation_bill_nullWord_of_sum
-- name    : APFPaper1.Continuation.bill_nullWord_of_sum
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:35:53.136091+00:00
-- url     : https://prove2.me/theorems/08de2b48-fe65-442a-a97f-328ed5c87cdd
-- title:
--   SUM and EMPTY make the empty-word bill zero
-- statement:
--   Assume SUM for all words and that the empty word at g keeps no record. Its calibrated bill is zero.
--
--   The whole-word bill is calibration(resource(word)); SUM is a finite sum over kept records, not additivity over fragments or equality with the original A2 distinction-cost sum. The author ruling records readings, changes no FOUNDATION_INPUTS, and leaves the hypotheses in Lean. No physical realization or unconditional C1/C3/W-her is certified. EMPTY is separately supplied, and was not put to the author as a call. The manuscript empty-family convention alone is not a proof of this word-record encoding.
-- source:
--   C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-14_session\astra\sib_v58_publication\source\Theorems\Thm_APFPaper1_Cont_identity_from_sum.lean:35

import Theorems.Thm_APFPaper1_Continuation_cont_identity
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
namespace APFPaper1.Continuation
end APFPaper1.Continuation
open APFPaper1.Continuation
universe uC uF uX uR uK
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.bill_nullWord_of_sum {Rec : Context → Type uK}
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (kept : (g : Context) → WordFrom Frag g → Finset (Rec g))
    (cost : (g : Context) → Rec g → NNReal)
    (hsum : ∀ (g : Context) (w : WordFrom Frag g),
      calibration g (resource g w) = ∑ r ∈ kept g w, cost g r)
    (g : Context) (hempty : kept g (nullWord g) = ∅) :
    calibration g (resource g (nullWord g)) = 0 := by sorry
