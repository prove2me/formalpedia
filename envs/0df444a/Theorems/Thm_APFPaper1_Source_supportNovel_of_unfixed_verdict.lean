-- Prove2me | Theorems.Thm_APFPaper1_Source_supportNovel_of_unfixed_verdict
-- name    : APFPaper1.Source.supportNovel_of_unfixed_verdict
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:10:27.765065+00:00
-- url     : https://prove2.me/theorems/439c28d9-cd2d-4f92-9bb3-a8a35e72d93e
-- title:
--   Supportnovel of unfixed verdict
-- statement:
--   Suppose sufficient support for d makes its verdict equal on states agreeing on that support. If every S-serving protocol within a positive eta of familyCost(S) leaves two states agreeing on all maintained records but disagreeing on d, then d is support-novel over S. Record soundness and the uniform near-optimal separation condition are explicit.
-- source:
--   Sib v44 Theorems/Thm_APFPaper1_support_novel_bridge.lean:25

import Definitions.Def_APFPaper1_FamilyCost

set_option autoImplicit false
namespace APFPaper1.Source
end APFPaper1.Source
open APFPaper1.Source

theorem APFPaper1.Source.supportNovel_of_unfixed_verdict {D P R Record Ω Val : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (reads : P → Record → Ω → Val) (verdict : D → Ω → Prop) (S : Finset D) (d : D)
    (hsound : ∀ (p : P) (sigma : Set Record), sufficient p sigma d →
      ∀ x y : Ω, (∀ r ∈ sigma, reads p r x = reads p r y) → (verdict d x ↔ verdict d y))
    (eta : ℝ) (heta : 0 < eta)
    (hunfixed : ∀ p : P,
      (∀ e ∈ S, ∃ sigma : Set Record,
        sigma ⊆ maintained p ∧ sufficient p sigma e ∧ usesToRealize p e sigma) →
      (calibration (wholeResource p) : ℝ) ≤
        familyCost wholeResource calibration maintained sufficient usesToRealize S + eta →
      ∃ x y : Ω, (∀ r ∈ maintained p, reads p r x = reads p r y) ∧ ¬ (verdict d x ↔ verdict d y)) :
    supportNovel wholeResource calibration maintained sufficient usesToRealize S d := by sorry
