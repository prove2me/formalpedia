-- Prove2me | solution 1 for levy_foundations_centeredPoissonTimeCountMartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:54:45.299892+00:00
-- url     : https://prove2.me/submissions/6d7d2c18-b59a-40de-90d5-083059f00467

import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_levy_foundations_prmFiltration
import Definitions.Def_levy_foundations_centeredPoissonTimeCount
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Theorems.Thm_levy_foundations_prmEvaluationMean
import Theorems.Thm_levy_foundations_measurablePRMEval
import Theorems.Thm_levy_foundations_prmEvalSigmaLe
import Theorems.Thm_levy_foundations_prmEvalSigmaApplyMeasurable
import Theorems.Thm_levy_foundations_prmIndepEvalSigma
import Theorems.Thm_levy_foundations_poissonTimeCountAdd
import Theorems.Thm_levy_foundations_prmFiltrationApply
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E)
    (hd : LevyFoundations.IsPoissonPointFamily K X
      ((volume : Measure ℝ).prod m) μ)
    {A : Set E} (hA : MeasurableSet A) (hfin : m A < ⊤) :
    MeasureTheory.Martingale
      (LevyFoundations.centeredPoissonTimeCount K X m A)
      (LevyFoundations.prmFiltration K X m
        hd.measurable_count hd.measurable_point) μ := by
  let ν : Measure (ℝ × E) := (volume : Measure ℝ).prod m
  have hBandFin (a b : ℝ) : ν (Set.Ioc a b ×ˢ A) < ⊤ := by
    dsimp only [ν]; rw [Measure.prod_prod, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hBandReal (a b : ℝ) (hab : a ≤ b) : (ν (Set.Ioc a b ×ˢ A)).toReal = (b - a) * (m A).toReal := by
    dsimp only [ν]; rw [Measure.prod_prod, Real.volume_Ioc,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  have hEvalInt (B : Set (ℝ × E)) (hB : MeasurableSet B)
      (hfinB : ν B < ⊤) :
      Integrable (fun ω => (LevyFoundations.poissonRandomMeasure K X ω B).toReal) μ := by
    exact integrable_toReal_of_lintegral_ne_top
      (levy_foundations_measurablePRMEval K X
        hd.measurable_count hd.measurable_point hB).aemeasurable
      (by rw [levy_foundations_prmEvaluationMean ν μ K X hd hB]
          exact hfinB.ne)
  have hEvalFinite (B : Set (ℝ × E)) (hB : MeasurableSet B) (hfinB : ν B < ⊤) :
      ∀ᵐ ω ∂μ, LevyFoundations.poissonRandomMeasure K X ω B < ⊤ :=
    ae_lt_top (levy_foundations_measurablePRMEval K X
      hd.measurable_count hd.measurable_point hB)
      (by rw [levy_foundations_prmEvaluationMean ν μ K X hd hB]; exact hfinB.ne)
  have hSigmaLe (R : Set (ℝ × E)) :
      LevyFoundations.prmEvalSigma K X ν R ≤ (inferInstance : MeasurableSpace Ω) :=
    levy_foundations_prmEvalSigmaLe K X ν R hd.measurable_count hd.measurable_point
  have hStrong (u : NNReal) :
      StronglyMeasurable[LevyFoundations.prmEvalSigma K X ν
        (Set.Iic (u : ℝ) ×ˢ Set.univ)]
        (LevyFoundations.centeredPoissonTimeCount K X m A u) := by
    change StronglyMeasurable[LevyFoundations.prmEvalSigma K X ν
      (Set.Iic (u : ℝ) ×ˢ Set.univ)]
      (fun ω => (LevyFoundations.poissonTimeCount K X A (u : ℝ) ω).toReal
        - (u : ℝ) * (m A).toReal)
    exact (((levy_foundations_prmEvalSigmaApplyMeasurable K X ν
      (measurableSet_Ioc.prod hA)
      (Set.prod_mono Set.Ioc_subset_Iic_self (Set.subset_univ A))
      (hBandFin 0 (u : ℝ))).ennreal_toReal).stronglyMeasurable).sub
      stronglyMeasurable_const
  have hInt (u : NNReal) :
      Integrable (LevyFoundations.centeredPoissonTimeCount K X m A u) μ := by
    change Integrable (fun ω =>
      (LevyFoundations.poissonTimeCount K X A (u : ℝ) ω).toReal
        - (u : ℝ) * (m A).toReal) μ
    exact (hEvalInt (Set.Ioc 0 (u : ℝ) ×ˢ A)
      (measurableSet_Ioc.prod hA) (hBandFin 0 (u : ℝ))).sub
      (integrable_const _)
  refine ⟨fun u => hStrong u, fun s t hst => ?_⟩
  simp only [levy_foundations_prmFiltrationApply]
  set fs := LevyFoundations.centeredPoissonTimeCount K X m A s with hfs
  set cb := fun ω => (LevyFoundations.poissonRandomMeasure K X ω
    (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A)).toReal
    - ((t : ℝ) - (s : ℝ)) * (m A).toReal with hcb
  have hincr :
      LevyFoundations.centeredPoissonTimeCount K X m A t =ᵐ[μ] fs + cb := by
    filter_upwards [hEvalFinite (Set.Ioc 0 (s : ℝ) ×ˢ A)
        (measurableSet_Ioc.prod hA) (hBandFin 0 (s : ℝ)),
      hEvalFinite (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A)
        (measurableSet_Ioc.prod hA) (hBandFin (s : ℝ) (t : ℝ))]
      with ω hωs hωband
    simp only [LevyFoundations.centeredPoissonTimeCount, hfs, hcb,
      Pi.add_apply]
    rw [levy_foundations_poissonTimeCountAdd K X A (s : ℝ) (t : ℝ)
      hA (NNReal.coe_nonneg s) (by exact_mod_cast hst) ω]
    simp only [LevyFoundations.poissonTimeCount]
    rw [ENNReal.toReal_add hωs.ne hωband.ne]
    ring
  have hle_s := hSigmaLe (Set.Iic (s : ℝ) ×ˢ Set.univ)
  have hle_band := hSigmaLe
    (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ)
  haveI : IsFiniteMeasure (μ.trim hle_s) := isFiniteMeasure_trim hle_s
  have hcbsm : StronglyMeasurable[LevyFoundations.prmEvalSigma K X ν
      (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ)] cb := by
    rw [hcb]
    exact (((levy_foundations_prmEvalSigmaApplyMeasurable K X ν
      (measurableSet_Ioc.prod hA)
      (Set.prod_mono (subset_refl _) (Set.subset_univ A))
      (hBandFin (s : ℝ) (t : ℝ))).ennreal_toReal).stronglyMeasurable).sub
      stronglyMeasurable_const
  have hindep : Indep
      (LevyFoundations.prmEvalSigma K X ν
        (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ))
      (LevyFoundations.prmEvalSigma K X ν
        (Set.Iic (s : ℝ) ×ˢ Set.univ)) μ :=
    levy_foundations_prmIndepEvalSigma ν μ K X hd
      (Set.Disjoint.set_prod_left
        (Set.Iic_disjoint_Ioc (le_refl (s : ℝ))).symm Set.univ Set.univ)
  have hcb_int : Integrable cb μ := by
    rw [hcb]
    exact (hEvalInt (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A)
      (measurableSet_Ioc.prod hA)
      (hBandFin (s : ℝ) (t : ℝ))).sub (integrable_const _)
  have hmean : (∫ ω, cb ω ∂μ) = 0 := by
    rw [hcb, integral_sub
        (hEvalInt (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A)
          (measurableSet_Ioc.prod hA) (hBandFin (s : ℝ) (t : ℝ)))
        (integrable_const _),
      integral_toReal
        (levy_foundations_measurablePRMEval K X
          hd.measurable_count hd.measurable_point (measurableSet_Ioc.prod hA)).aemeasurable
        (hEvalFinite (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A)
          (measurableSet_Ioc.prod hA) (hBandFin (s : ℝ) (t : ℝ))),
      levy_foundations_prmEvaluationMean ν μ K X hd
        (measurableSet_Ioc.prod hA),
      integral_const,
      hBandReal (s : ℝ) (t : ℝ) (by exact_mod_cast hst)]
    simp
  have hcb0 : μ[cb | LevyFoundations.prmEvalSigma K X ν
      (Set.Iic (s : ℝ) ×ˢ Set.univ)] =ᵐ[μ] 0 := by
    have hkey := MeasureTheory.condExp_indep_eq hle_band hle_s hcbsm hindep
    simp only [hmean] at hkey
    exact hkey
  refine (condExp_congr_ae hincr).trans ?_
  refine (condExp_add (hInt s) hcb_int _).trans ?_
  rw [condExp_of_stronglyMeasurable hle_s (hStrong s) (hInt s)]
  calc
    fs + μ[cb | LevyFoundations.prmEvalSigma K X ν
      (Set.Iic (s : ℝ) ×ˢ Set.univ)]
        =ᵐ[μ] fs + (0 : Ω → ℝ) := by
          filter_upwards [hcb0] with ω hω
          simp only [Pi.add_apply, hω, add_zero]
    _ = fs := add_zero fs