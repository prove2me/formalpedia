-- Prove2me | solution 1 for levy_foundations_projectiveFamily_content_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:26:19.095395+00:00
-- url     : https://prove2.me/submissions/12dd69a0-419b-4c07-92c3-27cbde69b35f

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Probability.ProductMeasure
import Definitions.Def_levy_foundations_projectiveFamily
import Theorems.Thm_levy_foundations_projectiveFamily_nonempty
import Theorems.Thm_LevyFoundations_compactProjectiveCylinders_nonempty
import Theorems.Thm_LevyFoundations_compactProjectiveThinning_nonempty

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset Filter
open scoped ENNReal Topology

set_option maxHeartbeats 800000
theorem solution
    {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)]
    [∀ i, TopologicalSpace (α i)]
    [∀ i, PolishSpace (α i)]
    [∀ i, BorelSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α)
    {B : ℕ → Set (∀ i, α i)}
    (hB : ∀ n, B n ∈ measurableCylinders α)
    (hB_anti : Antitone B) (hB_inter : ⋂ n, B n = ∅) :
    Tendsto (fun n => projectiveFamilyContent pf.consistent (B n))
      atTop (nhds 0) := by
  have hne : ∀ i, Nonempty (α i) :=
    fun i => levy_foundations_projectiveFamily_nonempty pf i
  choose I S mS B_eq using fun n ↦ (mem_measurableCylinders _).1 (hB n)
  classical
  let J : ℕ → Finset ι := fun n ↦ (Finset.range (n + 1)).sup I
  have hJ_mono : Monotone J :=
    fun _ _ hmn ↦ Finset.sup_mono (Finset.range_mono (by omega))
  have hIJ : ∀ n, I n ⊆ J n := fun n ↦
    Finset.le_sup (f := I) (Finset.mem_range.2 (by omega))
  let T : ∀ n, Set (∀ j : J n, α j) :=
    fun n ↦ Finset.restrict₂ (hIJ n) ⁻¹' S n
  have mT : ∀ n, MeasurableSet (T n) :=
    fun n ↦ (mS n).preimage (Finset.measurable_restrict₂ _)
  have B_eq' : ∀ n, B n = cylinder (J n) (T n) := fun n ↦ by
    rw [B_eq n]
    ext f
    simp [cylinder, T, Finset.restrict_def, Finset.restrict₂_def]
  have content_eq : ∀ n,
      projectiveFamilyContent pf.consistent (B n) =
        pf.measure (J n) (T n) := fun n ↦ by
    rw [B_eq']
    exact projectiveFamilyContent_cylinder pf.consistent (mT n)
  by_contra h_not_tendsto
  have h_mono : Antitone
      (fun n ↦ projectiveFamilyContent pf.consistent (B n)) :=
    fun _ _ hmn ↦ projectiveFamilyContent_mono pf.consistent
      (hB _) (hB _) (hB_anti hmn)
  rw [ENNReal.tendsto_atTop_zero] at h_not_tendsto
  push Not at h_not_tendsto
  obtain ⟨ε, hε_pos, h_freq⟩ := h_not_tendsto
  have h_lower : ∀ n, ε ≤ pf.measure (J n) (T n) := by
    intro n
    rw [← content_eq]
    obtain ⟨m, hmn, hm⟩ := h_freq n
    exact hm.le.trans (h_mono hmn)
  let ext_fun : ∀ {n}, (∀ j : J n, α j) → ∀ i, α i :=
    fun x i ↦ if h : i ∈ J _ then x ⟨i, h⟩ else (hne i).some
  have hT_anti : ∀ {n m} (hnm : n ≤ m),
      T m ⊆ Finset.restrict₂ (hJ_mono hnm) ⁻¹' T n := by
    intro n m hnm x hx
    have hf : ext_fun x ∈ B m := by
      rw [B_eq']
      simp only [mem_cylinder, ext_fun]
      convert hx using 1
      ext ⟨j, hj⟩
      simp [dif_pos hj]
    have hf_n := hB_anti hnm hf
    rw [B_eq'] at hf_n
    simp only [mem_cylinder] at hf_n
    simp only [Set.mem_preimage]
    convert hf_n using 1
    ext ⟨j, hj⟩
    simp [ext_fun, dif_pos (hJ_mono hnm hj)]
  choose K hK_sub hK_compact hK_diff using fun n ↦ by
    haveI := pf.prob (J n)
    exact MeasurableSet.exists_isCompact_sdiff_lt
      (μ := pf.measure (J n)) (mT n)
      (measure_ne_top (pf.measure (J n)) _)
      (ENNReal.div_pos hε_pos.ne' (ENNReal.pow_ne_top (by norm_num)) |>.ne' :
        ε / 2 ^ (n + 2) ≠ 0)
  let L : ∀ n, Set (∀ j : J n, α j) := fun n ↦
    K n ∩ ⋂ k : Fin n, Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' K k
  have hL_closed : ∀ n, IsClosed (L n) := fun n ↦
    (hK_compact n).isClosed |>.inter (isClosed_iInter fun k ↦
      (hK_compact k).isClosed.preimage (Finset.continuous_restrict₂ _))
  have hL_compact : ∀ n, IsCompact (L n) :=
    fun n ↦ (hK_compact n).of_isClosed_subset (hL_closed n) inter_subset_left
  have hL_sub_T : ∀ n, L n ⊆ T n :=
    fun n ↦ inter_subset_left.trans (hK_sub n)
  have hε_ne_top : ε ≠ ⊤ := by
    haveI := pf.prob (J 0)
    exact ne_top_of_le_ne_top (measure_ne_top _ _) (h_lower 0)
  have hL_nonempty : ∀ n, (L n).Nonempty := by
    exact LevyFoundations.compactProjectiveThinning_nonempty
      pf J hJ_mono T mT hT_anti K hK_compact
      ε hε_pos hε_ne_top h_lower (fun n ↦ (hK_diff n).le)
  have hL_restrict : ∀ {n m} (hnm : n ≤ m)
      (x : ∀ j : J m, α j),
      x ∈ L m → Finset.restrict₂ (hJ_mono hnm) x ∈ L n := by
    intro n m hnm x hx
    simp only [L, mem_inter_iff, mem_iInter] at hx ⊢
    refine ⟨?_, fun k ↦ ?_⟩
    · by_cases hnm' : n = m
      · subst hnm'
        exact hx.1
      · have : n < m := lt_of_le_of_ne hnm hnm'
        exact hx.2 (⟨n, this⟩ : Fin m)
    · have hkm : (k : ℕ) < m := lt_of_lt_of_le k.2 hnm
      exact hx.2 (⟨k, hkm⟩ : Fin m)
  obtain ⟨f, hf⟩ :=
    LevyFoundations.compactProjectiveCylinders_nonempty
      hne J hJ_mono L hL_closed hL_compact hL_nonempty hL_restrict
  have hfB : ∀ n, f ∈ B n := by
    intro n
    rw [B_eq']
    exact hL_sub_T n (Set.mem_iInter.1 hf n)
  have : f ∈ ⋂ n, B n := Set.mem_iInter.2 hfB
  rw [hB_inter] at this
  exact this.elim
