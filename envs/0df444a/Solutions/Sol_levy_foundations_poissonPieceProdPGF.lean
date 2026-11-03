-- Prove2me | solution 1 for levy_foundations_poissonPieceProdPGF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:00:02.974813+00:00
-- url     : https://prove2.me/submissions/675f9111-c65f-4045-875c-6833877ed4e6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Independence.Integration
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_prmPieceLaw
import Theorems.Thm_levy_foundations_poissonPGFSeries
import Theorems.Thm_levy_foundations_integralPieceMarksProduct
import Theorems.Thm_levy_foundations_poissonCountCellIntegral
import Theorems.Thm_levy_foundations_pieceCountEventProb
import Theorems.Thm_levy_foundations_poissonPieceProductIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k : ℕ) (w : E → ℂ)
    (hw : Measurable w) (hbdd : ∀ x, ‖w x‖ ≤ 1) :
    ∫ ω, ∏ n ∈ Finset.range (K k ω), w (X k n ω) ∂μ =
      Complex.exp
        ((m (LevyFoundations.prmPiece m k)).toReal *
          ((∫ x, w x ∂(LevyFoundations.prmPieceLaw m k)) - 1)) := by
  classical
  set s : ℕ → Set Ω := fun j => {ω | K k ω = j} with hs
  have hs_meas : ∀ j, MeasurableSet (s j) := fun j =>
    hd.measurable_count k (measurableSet_singleton j)
  have hs_disj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, hs, Set.mem_setOf_eq]
    intro ω h1 h2
    exact hab (h1 ▸ h2)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K k ω, rfl⟩
  have hInt :=
    levy_foundations_poissonPieceProductIntegrable m μ K X hd k w hw hbdd
  have hval := integral_iUnion
    (f := fun ω => ∏ n ∈ Finset.range (K k ω), w (X k n ω))
    hs_meas hs_disj (by rw [hunion]; exact hInt.integrableOn)
  rw [hunion, setIntegral_univ] at hval
  rw [hval]
  have hcell : ∀ j, ∫ ω in s j,
      ∏ n ∈ Finset.range (K k ω), w (X k n ω) ∂μ =
      ((poissonMeasure
        (m (LevyFoundations.prmPiece m k)).toNNReal).real {j} : ℂ) *
        (∫ x, w x ∂(LevyFoundations.prmPieceLaw m k)) ^ j := by
    intro j
    have hψmeas : Measurable (fun y : ℕ → E =>
        ∏ n ∈ Finset.range j, w (y n)) :=
      Finset.measurable_prod _ fun n _ => hw.comp (measurable_pi_apply n)
    have hEq : ∫ ω in s j,
        ∏ n ∈ Finset.range (K k ω), w (X k n ω) ∂μ =
        ∫ ω in s j, (fun y : ℕ → E =>
          ∏ n ∈ Finset.range j, w (y n)) (fun n => X k n ω) ∂μ := by
      refine setIntegral_congr_fun (hs_meas j) fun ω hω => ?_
      show (∏ n ∈ Finset.range (K k ω), w (X k n ω)) =
        ∏ n ∈ Finset.range j, w (X k n ω)
      rw [show K k ω = j from hω]
    rw [hEq, levy_foundations_poissonCountCellIntegral m μ K X
      hd k j (fun y : ℕ → E => ∏ n ∈ Finset.range j, w (y n)) hψmeas,
      levy_foundations_pieceCountEventProb m μ K X hd k j]
    congr 1
    exact levy_foundations_integralPieceMarksProduct
      m μ K X hd k j w hw hbdd
  simp_rw [hcell]
  exact levy_foundations_poissonPGFSeries
    (m (LevyFoundations.prmPiece m k)).toNNReal
    (∫ x, w x ∂(LevyFoundations.prmPieceLaw m k))
