-- Prove2me | solution 1 for levy_foundations_prmIndepEvalSigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:21:04.772205+00:00
-- url     : https://prove2.me/submissions/aa6c9274-ee4f-4608-8eea-427f00ea1cf1

import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.FinCases
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_prmEvalSigma
import Theorems.Thm_ProbabilityTheory_iIndep_prmEvalSigma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-! Transport the source independent-scattering theorem to the published evaluation σ-algebras. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {R S : Set E} (hRS : Disjoint R S) :
    Indep (LevyFoundations.prmEvalSigma K X m R)
      (LevyFoundations.prmEvalSigma K X m S) μ := by
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
  let F : Fin 2 → Set E := fun i => if i = 0 then R else S
  have hpair : Pairwise (Function.onFun Disjoint F) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint (F 0) (F 1)
      simpa [F] using hRS
    · change Disjoint (F 1) (F 0)
      simpa [F] using hRS.symm
    · exact (hij rfl).elim
  have hall := ProbabilityTheory.iIndep_prmEvalSigma hsource hpair
  have h01 := hall.indep (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  have hsrc : Indep (ProbabilityTheory.prmEvalSigma K X m R)
      (ProbabilityTheory.prmEvalSigma K X m S) μ := by
    simpa [F] using h01
  have heqR : ProbabilityTheory.prmEvalSigma K X m R =
      LevyFoundations.prmEvalSigma K X m R := by
    rfl
  have heqS : ProbabilityTheory.prmEvalSigma K X m S =
      LevyFoundations.prmEvalSigma K X m S := by
    rfl
  simpa only [heqR, heqS] using hsrc
