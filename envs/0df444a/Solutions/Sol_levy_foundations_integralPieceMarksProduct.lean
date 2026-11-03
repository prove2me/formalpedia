-- Prove2me | solution 1 for levy_foundations_integralPieceMarksProduct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:42:30.631243+00:00
-- url     : https://prove2.me/submissions/01c903a9-ecba-45df-85c6-e17261190cd1

import Mathlib.Probability.Independence.Integration
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_prmPieceLaw
import Theorems.Thm_levy_foundations_independentPieceMarks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k j : ℕ) (w : E → ℂ) (hw : Measurable w)
    (hbdd : ∀ x, ‖w x‖ ≤ 1) :
    ∫ ω, ∏ n ∈ Finset.range j, w (X k n ω) ∂μ =
      (∫ x, w x ∂(LevyFoundations.prmPieceLaw m k)) ^ j := by
  have hZ : iIndepFun (fun i : Fin j => X k (i : ℕ)) μ :=
    (levy_foundations_independentPieceMarks m μ K X hd k).precomp
      Fin.val_injective
  have hfun : (fun ω => ∏ n ∈ Finset.range j, w (X k n ω)) =
      fun ω => ∏ i : Fin j, w (X k (i : ℕ) ω) := by
    funext ω
    exact (Fin.prod_univ_eq_prod_range (fun n => w (X k n ω)) j).symm
  rw [hfun]
  rw [show (∫ ω, ∏ i : Fin j, w (X k (i : ℕ) ω) ∂μ) =
        ∏ i : Fin j, ∫ ω, w (X k (i : ℕ) ω) ∂μ from
      iIndepFun.integral_fun_prod_comp (f := fun _ : Fin j => w) hZ
        (fun i => (hd.measurable_point k (i : ℕ)).aemeasurable)
        (fun _ => hw.aestronglyMeasurable)]
  have heach : ∀ i : Fin j, ∫ ω, w (X k (i : ℕ) ω) ∂μ =
      ∫ x, w x ∂(LevyFoundations.prmPieceLaw m k) := by
    intro i
    rw [← (hd.law_point k (i : ℕ)).map_eq,
      integral_map (hd.measurable_point k (i : ℕ)).aemeasurable
        hw.aestronglyMeasurable]
  simp_rw [heach]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
