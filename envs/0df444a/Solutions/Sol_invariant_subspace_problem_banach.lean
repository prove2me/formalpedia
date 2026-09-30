-- Prove2me | solution 1 for invariant_subspace_problem_banach
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:46:39.235665+00:00
-- url     : https://prove2.me/submissions/320e5b46-ab7c-452c-8b96-b1accdaee57f

import Mathlib

set_option autoImplicit false

namespace RealAlgebraicInvariant

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

lemma countable_span_ne_top (hinfty : ¬FiniteDimensional ℝ H) (u : ℕ → H) :
    Submodule.span ℝ (Set.range u) ≠ ⊤ := by
  classical
  let F : ℕ → Submodule ℝ H := fun n => Submodule.span ℝ (u '' Set.Iio n)
  have hfinite (n : ℕ) : FiniteDimensional ℝ (F n) :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio n).image u)
  have hclosed (n : ℕ) : IsClosed (F n : Set H) := by
    letI := hfinite n
    exact (F n).closed_of_finiteDimensional
  have hmono : Monotone F := by
    intro a b hab
    apply Submodule.span_mono
    exact Set.image_mono (fun _ hx => lt_of_lt_of_le hx hab)
  have hspan : Submodule.span ℝ (Set.range u) = ⨆ n, F n := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨n, rfl⟩
      apply (le_iSup F (n + 1))
      exact Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
    · apply iSup_le
      intro n
      exact Submodule.span_mono (Set.image_subset_range _ _)
  intro htop
  have hcover : ⋃ n, (F n : Set H) = Set.univ := by
    rw [← Submodule.coe_iSup_of_directed F hmono.directed_le, ← hspan, htop]
    rfl
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have hFtop : F n = ⊤ := (F n).eq_top_of_nonempty_interior' hn
  apply hinfty
  letI := hfinite n
  apply FiniteDimensional.of_surjective (F n).subtype
  intro x
  exact ⟨⟨x, by rw [hFtop]; trivial⟩, rfl⟩

lemma invariant_exists (hinfty : ¬FiniteDimensional ℝ H) (T : H →L[ℝ] H) :
    ∃ S : Submodule ℝ H, S ≠ ⊥ ∧ S ≠ ⊤ ∧ ∀ x ∈ S, T x ∈ S := by
  classical
  have hnontrivial : ¬Subsingleton H := by
    intro h
    letI := h
    exact hinfty inferInstance
  letI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hnontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  let u : ℕ → H := fun n => (T ^ n) v
  let S := Submodule.span ℝ (Set.range u)
  refine ⟨S, ?_, countable_span_ne_top hinfty u, ?_⟩
  · intro hS
    have hvS : v ∈ S := by
      exact Submodule.subset_span ⟨0, by simp [u]⟩
    rw [hS] at hvS
    exact hv hvS
  · intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨n, rfl⟩
      apply Submodule.subset_span
      refine ⟨n + 1, ?_⟩
      change (T ^ (n + 1)) v = T ((T ^ n) v)
      rw [pow_succ']
      rfl
    · simpa using S.zero_mem
    · intro x y _ _ hx hy
      simpa using S.add_mem hx hy
    · intro a x _ hx
      simpa using S.smul_mem a hx

abbrev H2 := lp (fun _ : ℕ => ℝ) 2

lemma lp_infinite : ¬FiniteDimensional ℝ H2 := by
  classical
  let C : H2 →ₗ[ℝ] (ℕ → ℝ) :=
    { toFun := fun f => f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hli : LinearIndependent ℝ (fun n : ℕ => lp.single 2 n (1 : ℝ)) := by
    apply LinearIndependent.of_comp C
    exact Pi.linearIndependent_single_one ℕ ℝ
  intro h
  letI := h
  exact Module.Finite.not_linearIndependent_of_infinite _ hli

end RealAlgebraicInvariant

theorem solution :
    ∀ (T : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2),
      ∃ (V : Submodule ℝ (lp (fun _ : ℕ => ℝ) 2)),
        V ≠ ⊥ ∧ V ≠ ⊤ ∧ ∀ v ∈ V, T v ∈ V := by
  intro T
  exact RealAlgebraicInvariant.invariant_exists RealAlgebraicInvariant.lp_infinite T

#print axioms solution
