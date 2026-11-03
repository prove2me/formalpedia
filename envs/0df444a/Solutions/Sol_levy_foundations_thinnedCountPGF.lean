-- Prove2me | solution 1 for levy_foundations_thinnedCountPGF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:20:25.961707+00:00
-- url     : https://prove2.me/submissions/9097b106-dd63-4ec1-a466-1acfd7c31edf

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_levy_foundations_prodIteConstCard
import Theorems.Thm_levy_foundations_prmPieceLawProb
import Definitions.Def_levy_foundations_thinnedCount
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Theorems.Thm_levy_foundations_poissonPieceProdPGF
import Theorems.Thm_levy_foundations_prmPieceLawMassBridge

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
    (k : ℕ) {A : Set E} (hA : MeasurableSet A)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∫ ω, z ^ (LevyFoundations.thinnedCount K X A k ω) ∂μ =
      Complex.exp
        ((m (LevyFoundations.prmPiece m k ∩ A)).toReal * (z - 1))  := by
  classical
  haveI : IsProbabilityMeasure (LevyFoundations.prmPieceLaw m k) :=
    levy_foundations_prmPieceLawProb m k
  set w : E → ℂ := fun x => if x ∈ A then z else 1 with hw_def
  have hwmeas : Measurable w := Measurable.ite hA measurable_const measurable_const
  have hwbdd : ∀ x, ‖w x‖ ≤ 1 := by
    intro x
    simp only [hw_def]
    split_ifs with hx
    · exact hz
    · simp
  have hprod : ∀ ω, z ^ (LevyFoundations.thinnedCount K X A k ω) =
      ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    intro ω
    simp only [hw_def]
    rw [levy_foundations_prodIteConstCard
      (Finset.range (K k ω)) (fun n => X k n ω ∈ A) z]
    rfl
  simp_rw [hprod]
  rw [levy_foundations_poissonPieceProdPGF m μ K X hd k w hwmeas hwbdd]
  congr 1
  have hint : ∫ x, w x ∂(LevyFoundations.prmPieceLaw m k) =
      1 + (z - 1) * (LevyFoundations.prmPieceLaw m k).real A := by
    have hwrw : w = fun x => (1 : ℂ) + A.indicator (fun _ => z - 1) x := by
      funext x
      by_cases hx : x ∈ A
      · simp only [hw_def, Set.indicator_of_mem hx, if_pos hx]
        ring
      · simp only [hw_def, Set.indicator_of_notMem hx, if_neg hx]
        ring
    have hone : ∫ _ : E, (1 : ℂ) ∂(LevyFoundations.prmPieceLaw m k) = 1 := by
      simp
    rw [hwrw, integral_add (integrable_const 1)
      ((integrable_const (z - 1)).indicator hA),
      hone]
    have hind : ∫ x, A.indicator (fun _ => z - 1) x
        ∂(LevyFoundations.prmPieceLaw m k) =
        ((LevyFoundations.prmPieceLaw m k).real A : ℂ) * (z - 1) := by
      rw [integral_indicator_const (z - 1) hA]
      exact Complex.real_smul
    rw [hind]
    ring
  rw [hint]
  have halg : ((m (LevyFoundations.prmPiece m k)).toReal : ℂ) *
      ((1 + (z - 1) * ((LevyFoundations.prmPieceLaw m k).real A)) - 1) =
      (((m (LevyFoundations.prmPiece m k)).toReal *
        (LevyFoundations.prmPieceLaw m k).real A : ℝ) : ℂ) * (z - 1) := by
    push_cast
    ring
  rw [halg, levy_foundations_prmPieceLawMassBridge m k hA]
