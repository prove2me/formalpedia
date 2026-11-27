-- Prove2me | solution 1 for exists_pairing_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:34:44.968565+00:00
-- url     : https://prove2.me/submissions/3dea1c0a-f5d1-48b1-9c91-c1d3465188e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WedgeDetNz
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WedgeDetNz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem exists_dual_family_of_linearIndependent_orbital_bounds_conclusion (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    (ρ : ℕ) (z : Fin ρ → V) (hz : LinearIndependent K z) :
    ∃ φ : Fin ρ → (V →ₗ[K] K), (Matrix.of fun i k => φ i (z k)) = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend hz.repr
  refine ⟨fun i => (Finsupp.lapply i).comp g, ?_⟩
  ext i k
  have hk : z k ∈ Submodule.span K (Set.range z) := Submodule.subset_span ⟨k, rfl⟩
  have h1 : g (z k) = hz.repr ⟨z k, hk⟩ := by
    have := congrArg (fun f => f ⟨z k, hk⟩) hg
    simpa using this
  have h2 : hz.repr ⟨z k, hk⟩ = Finsupp.single k 1 := hz.repr_eq_single k _ rfl
  simp only [Matrix.of_apply, LinearMap.comp_apply, Finsupp.lapply_apply, h1, h2,
    Finsupp.single_apply, Matrix.one_apply]
  by_cases h : i = k
  · subst h; simp
  · simp [h, Ne.symm h]
end

set_option autoImplicit false

theorem _root_.solution : PI.WedgeDetNz := by
  intro K V _ _ _ ρ z hz
  obtain ⟨φ, hφ⟩ := exists_dual_family_of_linearIndependent_orbital_bounds_conclusion K V ρ z hz
  exact ⟨φ, by rw [hφ, Matrix.det_one]; exact one_ne_zero⟩
