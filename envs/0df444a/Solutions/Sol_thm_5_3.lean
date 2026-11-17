-- Prove2me | solution 1 for thm_5_3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:37:13.137483+00:00
-- url     : https://prove2.me/submissions/20e8dd2d-8369-4945-961d-bc04c2b34400

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic



/- Independence of discrete variables follows from factorisation on the singleton π-system. -/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

private theorem source_indepFun_of_point_mass_products
    {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsZeroOrProbabilityMeasure μ]
    (X Y : Ω → ℕ) (hX : Measurable X) (hY : Measurable Y)
    (hpmf : ∀ m n : ℕ,
       μ (X ⁻¹' ({m} : Set ℕ) ∩ Y ⁻¹' ({n} : Set ℕ)) =
         μ (X ⁻¹' ({m} : Set ℕ)) * μ (Y ⁻¹' ({n} : Set ℕ))) :
    ProbabilityTheory.IndepFun X Y μ := by
  let C : Set (Set ℕ) := Set.range fun n : ℕ => ({n} : Set ℕ)
  have hpi : IsPiSystem C := by
    intro s hs t ht hst
    rcases hs with ⟨m, rfl⟩
    rcases ht with ⟨n, rfl⟩
    rcases hst with ⟨x, hx⟩
    simp at hx
    rcases hx with ⟨hx1, hx2⟩
    have hmn : m = n := hx1.symm.trans hx2
    subst hmn
    simpa using (show ({m} : Set ℕ) ∈ C from ⟨m, rfl⟩)
  have hgen_top : MeasurableSpace.generateFrom C = (⊤ : MeasurableSpace ℕ) := by
    apply le_antisymm le_top
    intro s hs
    let f : s → Set ℕ := fun x => ({(x : ℕ)} : Set ℕ)
    have hs_eq : s = ⋃ x : s, f x := by
      ext n
      simp [f]
    rw [hs_eq]
    exact MeasurableSet.iUnion fun x => MeasurableSpace.measurableSet_generateFrom ⟨(x : ℕ), rfl⟩
  have hgen_borel : borel ℕ = MeasurableSpace.generateFrom C := by
    calc
      borel ℕ = (⊤ : MeasurableSpace ℕ) := borel_eq_top_of_discrete
      _ = MeasurableSpace.generateFrom C := hgen_top.symm
  have hgen : (inferInstance : MeasurableSpace ℕ) = MeasurableSpace.generateFrom C := by
    rw [BorelSpace.measurable_eq (α := ℕ)]
    exact hgen_borel
  let πX : Set (Set Ω) := Set.preimage X '' C
  let πY : Set (Set Ω) := Set.preimage Y '' C
  have hπX_meas : ∀ s ∈ πX, MeasurableSet s := by
    intro s hs
    rcases hs with ⟨A, hA, rfl⟩
    rcases hA with ⟨n, rfl⟩
    exact hX (measurableSet_singleton n)
  have hπY_meas : ∀ t ∈ πY, MeasurableSet t := by
    intro t ht
    rcases ht with ⟨A, hA, rfl⟩
    rcases hA with ⟨n, rfl⟩
    exact hY (measurableSet_singleton n)
  have hπX_pi : IsPiSystem πX := by
    convert hpi.comap X
    exact Eq.symm (Set.Subset.antisymm (fun ⦃a⦄ a_1 => a_1) fun ⦃a⦄ a_1 => a_1)
  have hπY_pi : IsPiSystem πY := by
    convert hpi.comap Y
    exact Eq.symm (Set.Subset.antisymm (fun ⦃a⦄ a_1 => a_1) fun ⦃a⦄ a_1 => a_1)
  have hπ_indep : ProbabilityTheory.IndepSets πX πY μ := by
    rw [ProbabilityTheory.IndepSets_iff]
    intro s t hs ht
    rcases hs with ⟨A, hA, rfl⟩
    rcases ht with ⟨B, hB, rfl⟩
    rcases hA with ⟨m, rfl⟩
    rcases hB with ⟨n, rfl⟩
    simpa using hpmf m n
  have hπX_gen : MeasurableSpace.comap X inferInstance = MeasurableSpace.generateFrom πX := by
    rw [hgen, MeasurableSpace.comap_generateFrom]
  have hπY_gen : MeasurableSpace.comap Y inferInstance = MeasurableSpace.generateFrom πY := by
    rw [hgen, MeasurableSpace.comap_generateFrom]
  have hIndep :
      ProbabilityTheory.Indep (MeasurableSpace.comap X inferInstance) (MeasurableSpace.comap Y inferInstance) μ := by
    rw [hπX_gen, hπY_gen]
    exact ProbabilityTheory.IndepSets.indep' hπX_meas hπY_meas hπX_pi hπY_pi hπ_indep
  exact (ProbabilityTheory.IndepFun_iff_Indep X Y μ).2 hIndep

theorem solution {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsZeroOrProbabilityMeasure μ]
    (X Y : Ω → ℕ) (hX : Measurable X) (hY : Measurable Y) :
    ProbabilityTheory.IndepFun X Y μ ↔
      ∀ m n : ℕ,
        μ (X ⁻¹' ({m} : Set ℕ) ∩ Y ⁻¹' ({n} : Set ℕ)) =
          μ (X ⁻¹' ({m} : Set ℕ)) * μ (Y ⁻¹' ({n} : Set ℕ)) := by
  constructor
  · intro hXY m n
    have hpre := (ProbabilityTheory.indepFun_iff_indepSet_preimage (μ := μ) hX hY).1 hXY
    exact
      (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
        (hX (measurableSet_singleton m))
        (hY (measurableSet_singleton n))
        (μ := μ)).1
        (hpre ({m} : Set ℕ) ({n} : Set ℕ) (measurableSet_singleton m) (measurableSet_singleton n))
  · intro hpmf
    exact source_indepFun_of_point_mass_products μ X Y hX hY hpmf
