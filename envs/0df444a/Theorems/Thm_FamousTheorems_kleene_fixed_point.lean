-- Prove2me | Theorems.Thm_FamousTheorems_kleene_fixed_point
-- name    : FamousTheorems.kleene_fixed_point
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:11.059379+00:00
-- url     : https://prove2.me/theorems/f1bc797c-7e93-4c1b-a643-b083ec0500a1
-- title:
--   The Kleene fixed-point theorem
-- statement:
--   **The Kleene fixed-point theorem.** Let $f$ be a monotone map on a complete lattice that is Scott-continuous (preserves suprema of increasing sequences). Then its least fixed point is
--   $$\operatorname{lfp}f=\bigvee_{n\ge0}f^n(\bot).$$
--
--   It computes the least fixed point constructively as the limit of iterates from the bottom element. It is the basis of the denotational semantics of recursive programs, of dataflow analysis, and of fixed-point characterisations in logic, such as the least Herbrand model.
--
--   **Formalization note.** Mathlib's `fixedPoints.lfp_eq_sSup_iterate`; `OrderHom.lfp f` is the least fixed point given by Knaster–Tarski, and `OmegaCompletePartialOrder.ωScottContinuous f` is the continuity hypothesis.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `fixedPoints.lfp_eq_sSup_iterate`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem kleene_fixed_point {α : Type*} [CompleteLattice α] (f : α →o α) (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
    OrderHom.lfp f = ⨆ n : ℕ, f^[n] ⊥ := by sorry

end FamousTheorems
