-- Prove2me | solution 1 for levy_foundations_thinnedCountLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:04:29.773017+00:00
-- url     : https://prove2.me/submissions/28734439-0f3e-4017-9ec4-2cb8d42824dd

import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_thinnedCount
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_prmPiece
import Theorems.Thm_levy_foundations_thinnedCountPGF
import Theorems.Thm_levy_foundations_thinnedCountMeasurable
import Theorems.Thm_levy_foundations_charFun_poissonMeasure_map

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : Set E) (hA : MeasurableSet A) (k : ℕ) :
    μ.map (LevyFoundations.thinnedCount K X A k) =
      poissonMeasure (m (LevyFoundations.prmPiece m k ∩ A)).toNNReal := by
  have hTA : Measurable (LevyFoundations.thinnedCount K X A k) :=
    levy_foundations_thinnedCountMeasurable K X A k
      (hd.measurable_count k) (hd.measurable_point k) hA
  haveI : IsProbabilityMeasure (μ.map (LevyFoundations.thinnedCount K X A k)) :=
    Measure.isProbabilityMeasure_map hTA.aemeasurable
  have hcast : (μ.map (LevyFoundations.thinnedCount K X A k)).map (Nat.cast : ℕ → ℝ) =
      (poissonMeasure (m (LevyFoundations.prmPiece m k ∩ A)).toNNReal).map
        (Nat.cast : ℕ → ℝ) := by
    haveI : IsProbabilityMeasure ((μ.map (LevyFoundations.thinnedCount K X A k)).map
        (Nat.cast : ℕ → ℝ)) :=
      Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable
    haveI : IsProbabilityMeasure ((poissonMeasure (m (LevyFoundations.prmPiece m k ∩ A)).toNNReal).map
        (Nat.cast : ℕ → ℝ)) :=
      Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable
    apply Measure.ext_of_charFun
    funext ξ
    have hchar : charFun ((μ.map (LevyFoundations.thinnedCount K X A k)).map
        (Nat.cast : ℕ → ℝ)) ξ =
        Complex.exp ((m (LevyFoundations.prmPiece m k ∩ A)).toReal *
          (Complex.exp (↑ξ * Complex.I) - 1)) := by
      rw [charFun_apply_real,
        integral_map (φ := (Nat.cast : ℕ → ℝ)) measurable_from_top.aemeasurable (by fun_prop),
        integral_map (φ := LevyFoundations.thinnedCount K X A k) hTA.aemeasurable
          (by fun_prop)]
      have hpow : ∀ ω, Complex.exp (↑ξ * ↑((LevyFoundations.thinnedCount K X A k ω : ℝ)) * Complex.I) =
          (Complex.exp (↑ξ * Complex.I)) ^ (LevyFoundations.thinnedCount K X A k ω) := by
        intro ω
        rw [show (↑ξ : ℂ) * ↑((LevyFoundations.thinnedCount K X A k ω : ℝ)) * Complex.I =
            ↑(LevyFoundations.thinnedCount K X A k ω) * (↑ξ * Complex.I) from by push_cast; ring,
          Complex.exp_nat_mul]
      simp_rw [hpow]
      exact levy_foundations_thinnedCountPGF m μ K X hd k hA
        (Complex.exp (↑ξ * Complex.I)) (le_of_eq (Complex.norm_exp_ofReal_mul_I ξ))
    rw [hchar, levy_foundations_charFun_poissonMeasure_map, ENNReal.coe_toNNReal_eq_toReal]
  have hEmb : MeasurableEmbedding (Nat.cast : ℕ → ℝ) :=
    ⟨Nat.cast_injective, measurable_from_top,
      fun {t} _ => (t.to_countable.image _).measurableSet⟩
  exact hEmb.map_injective hcast
