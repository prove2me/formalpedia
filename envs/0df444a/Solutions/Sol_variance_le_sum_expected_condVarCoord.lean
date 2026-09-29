-- Prove2me | solution 1 for variance_le_sum_expected_condVarCoord
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T17:26:43.384259+00:00
-- url     : https://prove2.me/submissions/f0bc8928-4e82-40ab-b08c-217b23a63e92

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_efron_stein_increment_le

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators


section ISec
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
variable (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

private lemma piFinset_empty_eq_bot :
    (Filtration.piFinset (X := α)) (∅ : Finset ι)
      = (⊥ : MeasurableSpace (∀ j, α j)) := by
  classical
  rw [Filtration.piFinset_eq_comap_restrict]
  let emptySet : Set ι := (↑(∅ : Finset ι) : Set ι)
  let z : (∀ i : emptySet, α i) := fun i =>
    False.elim (by exact (Finset.notMem_empty i.1) i.2)
  have hconst :
      (emptySet.domRestrict : (∀ j, α j) → (∀ i : emptySet, α i))
        = fun _ => z := by
    funext ω i
    exact False.elim ((Finset.notMem_empty i.1) i.2)
  rw [hconst, MeasurableSpace.comap_const]

omit [DecidableEq ι] in
private lemma piFinset_univ_eq_top :
    (Filtration.piFinset (X := α)) (Finset.univ : Finset ι)
      = (inferInstance : MeasurableSpace (∀ j, α j)) := by
  classical
  rw [Filtration.piFinset_eq_comap_restrict]
  let fullSet : Set ι := (↑(Finset.univ : Finset ι) : Set ι)
  apply le_antisymm
  · exact (Finset.measurable_restrict (Finset.univ : Finset ι)).comap_le
  · let inv : (∀ i : fullSet, α i) → (∀ j, α j) :=
      fun z j => z ⟨j, by dsimp [fullSet]; simp⟩
    have hinv_meas : Measurable inv := by
      fun_prop
    have hid :
        (fun ω : ∀ j, α j => ω) =
          inv ∘ fullSet.domRestrict := by
      funext ω j
      rfl
    calc
      (inferInstance : MeasurableSpace (∀ j, α j))
          = MeasurableSpace.comap (id : (∀ j, α j) → (∀ j, α j))
              (inferInstance : MeasurableSpace (∀ j, α j)) := by
              rw [MeasurableSpace.comap_id]
      _ = MeasurableSpace.comap (inv ∘ fullSet.domRestrict)
              (inferInstance : MeasurableSpace (∀ j, α j)) := by
              change MeasurableSpace.comap (fun ω : ∀ j, α j => ω)
                  (inferInstance : MeasurableSpace (∀ j, α j))
                = MeasurableSpace.comap (inv ∘ fullSet.domRestrict)
                  (inferInstance : MeasurableSpace (∀ j, α j))
              rw [← hid]
      _ = (MeasurableSpace.comap inv (inferInstance : MeasurableSpace (∀ j, α j))).comap
              fullSet.domRestrict := by
              rw [MeasurableSpace.comap_comp]
      _ ≤ MeasurableSpace.comap fullSet.domRestrict
              (inferInstance : MeasurableSpace (∀ i : fullSet, α i)) := by
              exact MeasurableSpace.comap_mono hinv_meas.comap_le

private lemma var_condExp_piFinset_le
    {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    ∀ s : Finset ι,
      variance ((Measure.pi μ)[Z | (Filtration.piFinset (X := α)) s]) (Measure.pi μ)
        ≤ ∑ i ∈ s, ∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ) := by
  classical
  refine Finset.induction ?hbase ?hstep
  · rw [piFinset_empty_eq_bot (α := α)]
    rw [condExp_bot]
    have hconst :
        variance (fun _ : (∀ j, α j) => ∫ x, Z x ∂(Measure.pi μ)) (Measure.pi μ) = 0 := by
      rw [variance_eq_integral aemeasurable_const]
      simp
    simp [hconst]
  · intro i s hi ih
    let F : Finset ι → MeasurableSpace (∀ j, α j) :=
      fun t => (Filtration.piFinset (X := α)) t
    set Y : (∀ j, α j) → ℝ := (Measure.pi μ)[Z | F (insert i s)] with hY
    have hYmem : MemLp Y 2 (Measure.pi μ) := by
      simpa [Y, hY] using (hZ.condExp (m := F (insert i s)) one_le_two)
    have hs_le : F s ≤ (inferInstance : MeasurableSpace (∀ j, α j)) := by
      simpa [F] using (Filtration.piFinset (X := α)).le s
    have hmono : F s ≤ F (insert i s) := by
      simpa [F] using
        (Filtration.piFinset (X := α)).mono (Finset.subset_insert i s)
    have hins_le : F (insert i s) ≤ (inferInstance : MeasurableSpace (∀ j, α j)) := by
      simpa [F] using (Filtration.piFinset (X := α)).le (insert i s)
    have hLOTV :
        (Measure.pi μ)[Var[Y; Measure.pi μ | F s]]
          + Var[(Measure.pi μ)[Y | F s]; Measure.pi μ]
            = Var[Y; Measure.pi μ] :=
      integral_condVar_add_variance_condExp hs_le hYmem
    have htower :
        (Measure.pi μ)[Y | F s] =ᵐ[Measure.pi μ] (Measure.pi μ)[Z | F s] := by
      rw [hY]
      exact condExp_condExp_of_le hmono hins_le
    have htv :
        Var[(Measure.pi μ)[Y | F s]; Measure.pi μ]
          = Var[(Measure.pi μ)[Z | F s]; Measure.pi μ] :=
      variance_congr htower
    rw [htv] at hLOTV
    have hdecomp :
        Var[Y; Measure.pi μ]
          = (Measure.pi μ)[Var[Y; Measure.pi μ | F s]]
              + Var[(Measure.pi μ)[Z | F s]; Measure.pi μ] := by
      linarith
    have hinc :
        (Measure.pi μ)[Var[Y; Measure.pi μ | F s]]
          ≤ ∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ) := by
      rw [hY]
      simpa [F] using efron_stein_increment_le (μ := μ) s i hi hZ
    calc
      variance ((Measure.pi μ)[Z | (Filtration.piFinset (X := α)) (insert i s)])
          (Measure.pi μ)
          = Var[Y; Measure.pi μ] := by simp [Y, hY, F]
      _ = (Measure.pi μ)[Var[Y; Measure.pi μ | F s]]
            + Var[(Measure.pi μ)[Z | F s]; Measure.pi μ] := hdecomp
      _ ≤ (∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ))
            + ∑ j ∈ s, ∫ ω, variance (fun x => Z (Function.update ω j x)) (μ j)
                ∂(Measure.pi μ) := add_le_add hinc (by simpa [F] using ih)
      _ = ∑ j ∈ insert i s, ∫ ω, variance (fun x => Z (Function.update ω j x)) (μ j)
                ∂(Measure.pi μ) := by
            rw [Finset.sum_insert hi]

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    variance Z (Measure.pi μ)
      ≤ ∑ i, ∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ) := by
  classical
  have hmain := var_condExp_piFinset_le (μ := μ) hZ (Finset.univ : Finset ι)
  have htop :
      (Measure.pi μ)[Z | (Filtration.piFinset (X := α)) (Finset.univ : Finset ι)]
        =ᵐ[Measure.pi μ] Z := by
    rw [piFinset_univ_eq_top (α := α)]
    exact condExp_of_aestronglyMeasurable' le_rfl hZ.aestronglyMeasurable
      (hZ.integrable one_le_two)
  have hvar :
      variance ((Measure.pi μ)[Z | (Filtration.piFinset (X := α)) (Finset.univ : Finset ι)])
          (Measure.pi μ)
        = variance Z (Measure.pi μ) :=
    variance_congr htop
  rw [hvar] at hmain
  simpa using hmain


end ISec
