-- Prove2me | Theorems.Thm_APFPaper1_Continuation_prefixMonotone_of_resource_mono
-- name    : APFPaper1.Continuation.prefixMonotone_of_resource_mono
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:41:35.653576+00:00
-- url     : https://prove2.me/theorems/10934db1-a8ba-4753-820b-a1a05ea7bd22
-- title:
--   Prefix resource order and monotone calibration imply monotone bills
-- statement:
--   The conclusion is the PrefixMonotone predicate for the supplied resource and calibration functions. It does not mention capacity, execution or raw inputs, and it does not prove the resource-prefix premise from the Supplement's definition of calibration. The result therefore provides a sufficient factorization of the conditional C3 hypothesis, not its physical supplier. Give each context's resource type a preorder. Suppose calibration preserves that order and every word prefix has resource no greater than the full word in the same starting context. Then calibrated whole-word resource is prefix-monotone. Both resource-prefix comparison and calibration monotonicity are explicit quantified hypotheses. Source: Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.
-- source:
--   Theorems/Thm_APFPaper1_Cont_prefix_restriction.lean, declaration at line 86 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}





/-! ### 5. Hereditary and whole-word classes -/

theorem APFPaper1.Continuation.prefixMonotone_of_resource_mono [∀ g, Preorder (R g)]
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (hcal : ∀ (g : Context) (a b : R g), a ≤ b → calibration g a ≤ calibration g b)
    (hres : ∀ (g : Context) (v w : WordFrom Frag g), IsPrefix v w → resource g v ≤ resource g w) :
    PrefixMonotone resource calibration := by sorry
