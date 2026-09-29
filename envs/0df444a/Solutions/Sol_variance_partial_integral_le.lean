-- Prove2me | solution 1 for variance_partial_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T07:08:11.43518+00:00
-- url     : https://prove2.me/submissions/85019708-8a89-4e32-8872-980f703f51a8

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

/-- **Partial-average variance contraction (two-factor product form).**
For `W ∈ L²(ρ ⊗ σ)` (`ρ`, `σ` probability measures), the partial average over the first
factor `g c = ∫ x, W (x, c) ∂ρ` has σ-variance at most the full variance of `W`:

  `variance (fun c => ∫ x, W (x, c) ∂ρ) σ ≤ variance W (ρ.prod σ)`.

This is the conditional-Jensen contraction `Var(E[W | σ(snd)]) ≤ Var(W)` with the conditional
expectation given the second factor identified as the partial integral over the first (the brick
`610550cc`, here inlined).  It is the per-step Jensen engine (step (d)) of the Doob-martingale proof
of Efron–Stein tensorization.  Source: van Handel APC550 §2.1; BLM Ch.3. -/
theorem solution {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (σ : Measure γ) [IsProbabilityMeasure σ]
    {W : β × γ → ℝ} (hW : MemLp W 2 (ρ.prod σ)) :
    variance (fun c => ∫ x, W (x, c) ∂ρ) σ ≤ variance W (ρ.prod σ) := by
  classical
  have hsnd_m : @Measurable _ _ (MeasurableSpace.comap Prod.snd inferInstance) _
      (Prod.snd : β × γ → γ) := Measurable.of_comap_le le_rfl
  have hm : MeasurableSpace.comap Prod.snd inferInstance ≤
      (inferInstance : MeasurableSpace (β × γ)) := measurable_snd.comap_le
  have hWint : Integrable W (ρ.prod σ) := hW.integrable one_le_two
  -- 610550cc (inlined): E[W | comap snd] =ᵐ fun p => ∫ x, W (x, p.2) ∂ρ.
  have hcondExp : (ρ.prod σ)[W | MeasurableSpace.comap Prod.snd inferInstance]
      =ᵐ[ρ.prod σ] fun p => ∫ x, W (x, p.2) ∂ρ := by
    set g0 : γ → ℝ := fun c => ∫ x, W (x, c) ∂ρ with hg0_def
    have hg0int : Integrable g0 σ := hWint.integral_prod_right
    set g0' : γ → ℝ := hg0int.aestronglyMeasurable.mk g0 with hg0'_def
    have hg0'sm : StronglyMeasurable g0' := hg0int.aestronglyMeasurable.stronglyMeasurable_mk
    have hg0eq : g0' =ᵐ[σ] g0 := hg0int.aestronglyMeasurable.ae_eq_mk.symm
    set g : β × γ → ℝ := fun p => g0 p.2 with hg_def
    have hsndmp : MeasurePreserving (Prod.snd : β × γ → γ) (ρ.prod σ) σ :=
      measurePreserving_snd
    have hgm_sm : StronglyMeasurable[MeasurableSpace.comap Prod.snd inferInstance]
        (fun p : β × γ => g0' p.2) := hg0'sm.comp_measurable hsnd_m
    have hg_ae : (fun p : β × γ => g0' p.2) =ᵐ[ρ.prod σ] g := by
      have := hsndmp.quasiMeasurePreserving.ae_eq_comp (g := g0') (g' := g0) hg0eq
      simpa [hg_def, Function.comp_def] using this
    have hgm : AEStronglyMeasurable[MeasurableSpace.comap Prod.snd inferInstance] g (ρ.prod σ) :=
      ⟨fun p => g0' p.2, hgm_sm, hg_ae.symm⟩
    have hgint : Integrable g (ρ.prod σ) := by
      have : Integrable (fun p : β × γ => g0 p.2) (ρ.prod σ) :=
        hsndmp.integrable_comp_of_integrable hg0int
      simpa [hg_def, Function.comp] using this
    refine (ae_eq_condExp_of_forall_setIntegral_eq hm hWint ?_ ?_ hgm).symm
    · intro s _ _; exact hgint.integrableOn
    · intro s hs _
      obtain ⟨t, ht, rfl⟩ := hs
      have hpre : (Prod.snd : β × γ → γ) ⁻¹' t = Set.univ ×ˢ t := by
        ext ⟨b, c⟩; simp
      rw [hpre]
      have hrestrict : (ρ.prod σ).restrict (Set.univ ×ˢ t)
          = (ρ.restrict Set.univ).prod (σ.restrict t) := (Measure.prod_restrict _ _).symm
      rw [hrestrict, Measure.restrict_univ]
      have hWon : Integrable W (ρ.prod (σ.restrict t)) := by
        have := hWint.integrableOn (s := Set.univ ×ˢ t)
        rwa [IntegrableOn, hrestrict, Measure.restrict_univ] at this
      have hgon : Integrable g (ρ.prod (σ.restrict t)) := by
        have := hgint.integrableOn (s := Set.univ ×ˢ t)
        rwa [IntegrableOn, hrestrict, Measure.restrict_univ] at this
      rw [integral_prod_symm g hgon, integral_prod_symm W hWon]
      refine integral_congr_ae (.of_forall (fun c => ?_))
      simp only [hg_def, hg0_def, integral_const, probReal_univ, smul_eq_mul, one_mul]
  -- Outer conditional-Jensen contraction Var(E[W|m]) ≤ Var(W) (law of total variance, inlined).
  have hcontract : Var[(ρ.prod σ)[W | MeasurableSpace.comap Prod.snd inferInstance]; ρ.prod σ]
      ≤ Var[W; ρ.prod σ] := by
    have hkey : (ρ.prod σ)[Var[W; ρ.prod σ | MeasurableSpace.comap Prod.snd inferInstance]]
        + Var[(ρ.prod σ)[W | MeasurableSpace.comap Prod.snd inferInstance]; ρ.prod σ]
        = Var[W; ρ.prod σ] :=
      integral_condVar_add_variance_condExp hm hW
    have hcv_nonneg : (0 : β × γ → ℝ)
        ≤ᵐ[ρ.prod σ] Var[W; ρ.prod σ | MeasurableSpace.comap Prod.snd inferInstance] := by
      have hsq : (0 : β × γ → ℝ) ≤ᵐ[ρ.prod σ]
          (fun p => (W p - ((ρ.prod σ)[W | MeasurableSpace.comap Prod.snd inferInstance]) p) ^ 2) :=
        Filter.Eventually.of_forall (fun p => sq_nonneg _)
      exact condExp_nonneg hsq
    have hnn : 0 ≤ (ρ.prod σ)[Var[W; ρ.prod σ | MeasurableSpace.comap Prod.snd inferInstance]] :=
      integral_nonneg_of_ae hcv_nonneg
    linarith
  -- Identify the condExp's variance with the partial-integral's, then drop the first factor.
  have hvarEq1 : Var[(ρ.prod σ)[W | MeasurableSpace.comap Prod.snd inferInstance]; ρ.prod σ]
      = Var[(fun p : β × γ => ∫ x, W (x, p.2) ∂ρ); ρ.prod σ] := variance_congr hcondExp
  have mpsnd : MeasurePreserving (Prod.snd : β × γ → γ) (ρ.prod σ) σ :=
    MeasureTheory.measurePreserving_snd
  have hgae : AEMeasurable (fun c => ∫ x, W (x, c) ∂ρ) σ := by
    have hint : Integrable (fun c => ∫ x, W (x, c) ∂ρ) σ := hWint.integral_prod_right
    exact hint.aemeasurable
  have hvarEq2 : Var[(fun p : β × γ => ∫ x, W (x, p.2) ∂ρ); ρ.prod σ]
      = variance (fun c => ∫ x, W (x, c) ∂ρ) σ := by
    have hcomp : (fun p : β × γ => ∫ x, W (x, p.2) ∂ρ)
        = (fun c => ∫ x, W (x, c) ∂ρ) ∘ Prod.snd := rfl
    rw [hcomp]
    exact mpsnd.variance_fun_comp hgae
  rw [hvarEq1, hvarEq2] at hcontract
  exact hcontract
