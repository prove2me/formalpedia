-- Prove2me | solution 2 for replicated_centers_intersection_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:20:49.409856+00:00
-- url     : https://prove2.me/submissions/593fb97a-5888-4e33-9c17-43b2ccb0eeca

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise
variable {d : ℕ}


theorem solution {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D F : Set (EuclideanSpace ℝ (Fin d))}
    (hF_sub : F ⊆ D) (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) :
    latticeReplicatedCenters (d := d) Λ F ∩ D = F := by
  ext x; constructor
  · rintro ⟨hx, hxD⟩
    obtain ⟨g, f, hf, rfl⟩ := mem_replicated_centers_iff.1 hx
    obtain ⟨g0, _, huniq⟩ := hD_unique_covers f
    have h1 := huniq g hxD
    have h2 := huniq 0 (by simpa using hF_sub hf)
    have : g = 0 := h1.trans h2.symm
    subst this
    simpa using hf
  · intro hx
    exact ⟨mem_replicated_centers_iff.2 ⟨0, x, hx, by simp⟩, hF_sub hx⟩

