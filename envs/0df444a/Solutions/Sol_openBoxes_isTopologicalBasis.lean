-- Prove2me | solution 1 for openBoxes_isTopologicalBasis
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:04:13.591297+00:00
-- url     : https://prove2.me/submissions/cd66ca2b-35cb-4c89-886c-f17466d5f044

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

-- import Mathlib.Data.Real.Pointwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory MeasurableSpace

open scoped Pointwise


/-- Choose a real open interval inside each coordinate neighbourhood. -/
private theorem choose_pi_box_intervals {d : ℕ} (x : Fin d → ℝ)
    (V : Fin d → Set ℝ)
    (hV : ∀ i, IsOpen (V i) ∧ x i ∈ V i) :
    ∀ i : Fin d, ∃ a b : ℝ, a < x i ∧ x i < b ∧ Ioo a b ⊆ V i := by
  intro i
  rcases Metric.isOpen_iff.mp (hV i).1 (x i) (hV i).2 with ⟨r, hr, hball⟩
  refine ⟨x i - r / 2, x i + r / 2, by linarith, by linarith, ?_⟩
  intro y hy
  apply hball
  change dist y (x i) < r
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hy.1, hr], by linarith [hy.2, hr]⟩

theorem solution (d : ℕ) :
    TopologicalSpace.IsTopologicalBasis (openBoxes d) := by
  classical
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro s ⟨a, b, hab, rfl⟩
    exact isOpen_set_pi Set.finite_univ (fun i _ => isOpen_Ioo)
  · intro x U hx hU
    rcases isOpen_pi_iff'.mp hU x hx with ⟨V, hV, hVU⟩
    have hchoose := choose_pi_box_intervals x V hV
    choose a b ha hb hsub using hchoose
    refine ⟨Set.pi Set.univ (fun i => Ioo (a i) (b i)),
      ⟨a, b, fun i => lt_trans (ha i) (hb i), rfl⟩, ?_, ?_⟩
    · intro i _hi
      exact ⟨ha i, hb i⟩
    · intro y hy
      apply hVU
      intro i hi
      exact hsub i (hy i hi)