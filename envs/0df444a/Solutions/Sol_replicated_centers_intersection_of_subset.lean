-- Prove2me | solution 1 for replicated_centers_intersection_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/b99be71a-18dd-40b2-8199-9b84a38f186e

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
theorem _root_.solution {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D F : Set (EuclideanSpace ℝ (Fin d))}
    (hF_sub : F ⊆ D) (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) :
    latticeReplicatedCenters (d := d) Λ F ∩ D = F := by
  ext x
  constructor
  · rintro ⟨hx, hxD⟩
    rcases (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F)).1 hx with
      ⟨g, f, hf, hxf⟩
    obtain ⟨g₀, hg₀, hunique⟩ := hD_unique_covers f
    have hg : g = g₀ := hunique g (show g +ᵥ f ∈ D from hxf ▸ hxD)
    have hzero : (0 : Λ) = g₀ := hunique 0 (by simpa using hF_sub hf)
    have : g = 0 := hg.trans hzero.symm
    simpa [hxf, this] using hf
  · intro hx
    refine ⟨?_, hF_sub hx⟩
    exact (mem_replicated_centers_iff (d := d) (Λ := Λ) (F := F)).2
      ⟨0, x, hx, by simp⟩
