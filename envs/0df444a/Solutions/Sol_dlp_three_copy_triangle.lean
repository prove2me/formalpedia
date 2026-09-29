-- Prove2me | solution 1 for dlp_three_copy_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T03:54:36.198604+00:00
-- url     : https://prove2.me/submissions/b97efaf2-4220-497e-abcf-31b152685df8

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Normed.Module.Basic
open MeasureTheory
open scoped ENNReal

theorem solution
    {α : Type*} [MeasurableSpace α]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
      [BorelSpace V] [SecondCountableTopology V]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → V) (hf : Measurable f) (t : ℝ) :
    (Measure.pi (fun _ : Fin 3 => μ)).real {g | t ≤ ‖f (g 0)‖}
      ≤ 3 * (Measure.pi (fun _ : Fin 3 => μ)).real
              {g | 2 * t / 3 ≤ ‖f (g 0) + f (g 1)‖} := by
  classical
  set ν : Measure (Fin 3 → α) := Measure.pi (fun _ : Fin 3 => μ) with hν
  have hprob : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  have hmeas_eval : ∀ i : Fin 3, Measurable (fun g : Fin 3 → α => g i) :=
    fun i => measurable_pi_apply i
  set S : Set (Fin 3 → α) := {g | t ≤ ‖f (g 0)‖} with hS
  set E01 : Set (Fin 3 → α) := {g | 2 * t / 3 ≤ ‖f (g 0) + f (g 1)‖} with hE01
  set E02 : Set (Fin 3 → α) := {g | 2 * t / 3 ≤ ‖f (g 0) + f (g 2)‖} with hE02
  set E12 : Set (Fin 3 → α) := {g | 2 * t / 3 ≤ ‖f (g 1) + f (g 2)‖} with hE12
  have hmS : MeasurableSet S := by
    apply measurableSet_le measurable_const
    exact Measurable.norm (hf.comp (hmeas_eval 0))
  have hmE01 : MeasurableSet E01 := by
    apply measurableSet_le measurable_const
    exact Measurable.norm ((hf.comp (hmeas_eval 0)).add (hf.comp (hmeas_eval 1)))
  have hmE02 : MeasurableSet E02 := by
    apply measurableSet_le measurable_const
    exact Measurable.norm ((hf.comp (hmeas_eval 0)).add (hf.comp (hmeas_eval 2)))
  have hmE12 : MeasurableSet E12 := by
    apply measurableSet_le measurable_const
    exact Measurable.norm ((hf.comp (hmeas_eval 1)).add (hf.comp (hmeas_eval 2)))
  have hsub : S ⊆ E01 ∪ E02 ∪ E12 := by
    intro g hg
    rw [hS, Set.mem_setOf_eq] at hg
    by_contra hcon
    rw [Set.mem_union, Set.mem_union] at hcon
    push_neg at hcon
    obtain ⟨⟨h01, h02⟩, h12⟩ := hcon
    rw [hE01, Set.mem_setOf_eq, not_le] at h01
    rw [hE02, Set.mem_setOf_eq, not_le] at h02
    rw [hE12, Set.mem_setOf_eq, not_le] at h12
    have hnorm2' : ‖f (g 0) + f (g 0)‖ = 2 * ‖f (g 0)‖ := by
      have : f (g 0) + f (g 0) = (2:ℝ) • f (g 0) := by rw [two_smul]
      rw [this, norm_smul, Real.norm_ofNat]
    have htri : ‖f (g 0) + f (g 0)‖
        ≤ ‖f (g 0) + f (g 1)‖ + ‖f (g 0) + f (g 2)‖ + ‖f (g 1) + f (g 2)‖ := by
      have heq : f (g 0) + f (g 0)
          = (f (g 0) + f (g 1)) + (f (g 0) + f (g 2)) - (f (g 1) + f (g 2)) := by abel
      rw [heq]
      calc ‖(f (g 0) + f (g 1)) + (f (g 0) + f (g 2)) - (f (g 1) + f (g 2))‖
          ≤ ‖(f (g 0) + f (g 1)) + (f (g 0) + f (g 2))‖ + ‖f (g 1) + f (g 2)‖ := norm_sub_le _ _
        _ ≤ (‖f (g 0) + f (g 1)‖ + ‖f (g 0) + f (g 2)‖) + ‖f (g 1) + f (g 2)‖ := by
              gcongr; exact norm_add_le _ _
    rw [hnorm2'] at htri
    linarith
  have hbound : ν.real S ≤ ν.real E01 + ν.real E02 + ν.real E12 := by
    calc ν.real S ≤ ν.real (E01 ∪ E02 ∪ E12) := by
            apply measureReal_mono hsub
        _ ≤ ν.real (E01 ∪ E02) + ν.real E12 := measureReal_union_le _ _
        _ ≤ (ν.real E01 + ν.real E02) + ν.real E12 := by
              gcongr; exact measureReal_union_le _ _
  have hperm : ∀ e : Equiv.Perm (Fin 3),
      MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => α) e) ν ν := by
    intro e
    have := measurePreserving_piCongrLeft (fun _ : Fin 3 => μ) e
    rw [hν]; simpa using this
  have hact : ∀ (e : Equiv.Perm (Fin 3)) (g : Fin 3 → α) (i : Fin 3),
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => α) e) g i = g (e.symm i) := by
    intro e g i
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    exact cast_eq _ _
  set T1 := MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => α) (Equiv.swap (1 : Fin 3) 2) with hT1
  have hpre1 : (T1 : (Fin 3 → α) → (Fin 3 → α)) ⁻¹' E01 = E02 := by
    ext g
    simp only [Set.mem_preimage, hE01, hE02, Set.mem_setOf_eq]
    rw [hact (Equiv.swap (1:Fin 3) 2) g 0, hact (Equiv.swap (1:Fin 3) 2) g 1]
    rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide),
      Equiv.swap_apply_left]
  have hE02eq : ν.real E02 = ν.real E01 := by
    rw [← hpre1]
    exact (hperm (Equiv.swap (1:Fin 3) 2)).measureReal_preimage hmE01.nullMeasurableSet
  set c : Equiv.Perm (Fin 3) := Equiv.swap (0:Fin 3) 1 * Equiv.swap (1:Fin 3) 2 with hc
  set T2 := MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => α) c.symm with hT2
  have hpre2 : (T2 : (Fin 3 → α) → (Fin 3 → α)) ⁻¹' E01 = E12 := by
    ext g
    simp only [Set.mem_preimage, hE01, hE12, Set.mem_setOf_eq]
    rw [hact c.symm g 0, hact c.symm g 1]
    have h0 : (c.symm).symm 0 = (1 : Fin 3) := by rw [Equiv.symm_symm]; decide
    have h1 : (c.symm).symm 1 = (2 : Fin 3) := by rw [Equiv.symm_symm]; decide
    rw [h0, h1]
  have hE12eq : ν.real E12 = ν.real E01 := by
    rw [← hpre2]
    exact (hperm c.symm).measureReal_preimage hmE01.nullMeasurableSet
  rw [hE02eq, hE12eq] at hbound
  calc ν.real S ≤ ν.real E01 + ν.real E01 + ν.real E01 := hbound
    _ = 3 * ν.real E01 := by ring
