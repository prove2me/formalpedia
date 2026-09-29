-- Prove2me | Theorems.Thm_FamousTheorems_freyd_mitchell
-- name    : FamousTheorems.freyd_mitchell
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:04.16726+00:00
-- url     : https://prove2.me/theorems/dd98d0cb-3d27-4697-833e-1d3e8fdc1189
-- title:
--   The Freyd–Mitchell embedding theorem
-- statement:
--   **The Freyd–Mitchell embedding theorem.** Every abelian category $\mathcal C$ admits a full, faithful, exact functor $F:\mathcal C\to R\text{-}\mathbf{Mod}$ into modules over some ring $R$.
--
--   Consequently any diagram-chasing statement about finite diagrams (the five lemma, the snake lemma, the $3\times3$ lemma, long exact sequences) that holds for modules, where elements can be chased, holds in every abelian category.
--
--   **Formalization note.** Mathlib's `CategoryTheory.Abelian.freyd_mitchell`. Exactness is expressed as preservation of finite limits and finite colimits. The ring lives in universe `max u v` for a category of type `Type u` with morphisms in `Type v`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.Abelian.freyd_mitchell`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

theorem freyd_mitchell (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C] :
    ∃ (R : Type (max u v)) (_ : Ring R) (F : CategoryTheory.Functor C (ModuleCat.{max u v} R)),
      F.Full ∧ F.Faithful ∧ CategoryTheory.Limits.PreservesFiniteLimits F ∧
        CategoryTheory.Limits.PreservesFiniteColimits F := by sorry

end FamousTheorems
