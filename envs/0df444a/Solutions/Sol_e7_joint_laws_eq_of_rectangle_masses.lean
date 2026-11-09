-- Prove2me | solution 1 for e7_joint_laws_eq_of_rectangle_masses
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T08:45:54.121069+00:00
-- url     : https://prove2.me/submissions/d7f313e4-1d04-473e-8c00-66dbc1b54627

import Mathlib

open MeasureTheory Set
open scoped ENNReal

/-- Two probability measures on a finite product agree if their masses agree on all
measurable rectangles. -/
theorem solution {ι E Ω Ω' : Type*} [Fintype ι] [MeasurableSpace E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Ω → ι → E) (y : Ω' → ι → E)
    (hx : Measurable x) (hy : Measurable y)
    (hrect : ∀ B : ι → Set E, (∀ i, MeasurableSet (B i)) →
      P {ω | ∀ i, x ω i ∈ B i} = Q {ω | ∀ i, y ω i ∈ B i}) :
    Measure.map x P = Measure.map y Q := by
  let C : Set (Set (ι → E)) := Set.pi univ '' Set.pi univ (fun _ => {s : Set E | MeasurableSet s})
  have hgen : (inferInstance : MeasurableSpace (ι → E)) = MeasurableSpace.generateFrom C := by
    change (inferInstance : MeasurableSpace (ι → E)) =
      MeasurableSpace.generateFrom
        (Set.pi univ '' Set.pi univ (fun _ : ι => {s : Set E | MeasurableSet s}))
    rw [generateFrom_pi]
  have hpi : IsPiSystem C := by
    rintro _ ⟨B, hB, rfl⟩ _ ⟨B', hB', rfl⟩ _
    refine ⟨fun i => B i ∩ B' i, ?_, ?_⟩
    · rw [Set.mem_pi] at hB hB' ⊢
      intro i _
      exact (hB i (Set.mem_univ i)).inter (hB' i (Set.mem_univ i))
    · ext z
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_inter_iff, forall_and]
  have hspan : ⋃ i : ℕ, (Set.univ : Set (ι → E)) = univ := by
    rw [Set.iUnion_const]
  have hmem : ∀ i : ℕ, (Set.univ : Set (ι → E)) ∈ C := by
    intro _
    refine ⟨fun _ => Set.univ, ?_, ?_⟩
    · rw [Set.mem_pi]
      intro i _
      exact MeasurableSet.univ
    · simp
  have hfin : ∀ i : ℕ, Measure.map x P (Set.univ : Set (ι → E)) ≠ ∞ := by
    intro _
    rw [Measure.map_apply hx MeasurableSet.univ]
    simp
  apply Measure.ext_of_generateFrom_of_iUnion C (fun _ => Set.univ) hgen hpi hspan hmem hfin
  intro s hs
  obtain ⟨B, hB, rfl⟩ := hs
  rw [Set.mem_pi] at hB
  rw [Measure.map_apply hx, Measure.map_apply hy]
  · have hxpre : x ⁻¹' (Set.pi Set.univ B) = {ω | ∀ i, x ω i ∈ B i} := by
      ext ω; simp [Set.mem_pi]
    have hypre : y ⁻¹' (Set.pi Set.univ B) = {ω | ∀ i, y ω i ∈ B i} := by
      ext ω; simp [Set.mem_pi]
    rw [hxpre, hypre]
    exact hrect B (fun i => hB i (Set.mem_univ i))
  · exact MeasurableSet.univ_pi (fun i => hB i (Set.mem_univ i))
  · exact MeasurableSet.univ_pi (fun i => hB i (Set.mem_univ i))
