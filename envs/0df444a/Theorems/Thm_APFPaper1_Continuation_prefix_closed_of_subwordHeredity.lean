-- Prove2me | Theorems.Thm_APFPaper1_Continuation_prefix_closed_of_subwordHeredity
-- name    : APFPaper1.Continuation.prefix_closed_of_subwordHeredity
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:40:17.413454+00:00
-- url     : https://prove2.me/theorems/71cdb0ae-f449-43ca-8e9b-5c65c0d2cbee
-- title:
--   W-her implies C3 for whole-word Cont
-- statement:
--   Assume SubwordHeredity for Cont with admissible subwords defined by existential Cont membership. Any prefix of a continuation from x remains a continuation from x; the bill is independent of the raw input. The admissible subword class is fixed to existential Cont membership, not arbitrary Amb. Execution of a prefix comes from the original input; its state-independent bill comes from W-her. W-her remains a structural hypothesis, not a foundation consequence. No converse is claimed.
-- source:
--   C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-14_session\astra\sib_v58_publication\source\Theorems\Thm_APFPaper1_Cont_subword_gives_prefix.lean:30

import Definitions.Def_APFPaper1_ContextualEquivalence

set_option autoImplicit false
namespace APFPaper1.Continuation
end APFPaper1.Continuation
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.prefix_closed_of_subwordHeredity
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (hher : SubwordHeredity (Cont step resource calibration C)
      (fun g h M => ∃ x : Raw g, Cont step resource calibration C g x ⟨h, M⟩))
    (g : Context) (x : Raw g) (v w : WordFrom Frag g) (hpre : IsPrefix v w)
    (hw : Cont step resource calibration C g x w) :
    Cont step resource calibration C g x v := by sorry
