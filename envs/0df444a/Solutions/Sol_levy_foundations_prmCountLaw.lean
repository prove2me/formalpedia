-- Prove2me | solution 1 for levy_foundations_prmCountLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:04:01.255982+00:00
-- url     : https://prove2.me/submissions/db4b56d9-dd5d-43d1-b993-772d77ae3000

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_map_poissonRandomMeasure_apply

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {A : Set E} (hA : MeasurableSet A) (hfin : m A < ⊤) :
    μ.map (fun ω => LevyFoundations.poissonRandomMeasure K X ω A) =
      (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ENNReal) := by
  have hsource : ProbabilityTheory.IsPoissonPointFamily K X m μ := by
    refine ⟨hd.measurable_count, hd.measurable_point, ?_, ?_, ?_⟩
    · apply (ProbabilityTheory.iIndepFun_iff_iIndep
        (fun i : ℕ ⊕ ℕ × ℕ =>
          ProbabilityTheory.instMeasurableSpacePointFamilyIndexType E i)
        (ProbabilityTheory.pointFamilyCombined K X) μ).2
      have hind := (ProbabilityTheory.iIndepFun_iff_iIndep
        (fun i : ℕ ⊕ ℕ × ℕ =>
          LevyFoundations.instPointFamilyIndexMeasurable E i)
        (LevyFoundations.pointFamilyCombined K X) μ).1 hd.indep
      have heq : (fun i : ℕ ⊕ ℕ × ℕ =>
          MeasurableSpace.comap (LevyFoundations.pointFamilyCombined K X i)
            (LevyFoundations.instPointFamilyIndexMeasurable E i)) =
          (fun i => MeasurableSpace.comap (ProbabilityTheory.pointFamilyCombined K X i)
            (ProbabilityTheory.instMeasurableSpacePointFamilyIndexType E i)) := by
          funext i
          cases i <;> rfl
      rw [heq] at hind
      exact hind
    · intro k
      simpa only [ProbabilityTheory.prmPiece, LevyFoundations.prmPiece] using hd.law_count k
    · intro k n
      convert hd.law_point k n using 1
      classical
      unfold ProbabilityTheory.prmPieceLaw LevyFoundations.prmPieceLaw
      simp only [ProbabilityTheory.prmPiece, LevyFoundations.prmPiece]
      split_ifs with h
      · rfl
      · ext s hs
        first | rfl | simp [Measure.smul_apply]
  have hmap := ProbabilityTheory.map_poissonRandomMeasure_apply hsource hA hfin
  simpa only [ProbabilityTheory.poissonRandomMeasure,
    LevyFoundations.poissonRandomMeasure] using hmap
