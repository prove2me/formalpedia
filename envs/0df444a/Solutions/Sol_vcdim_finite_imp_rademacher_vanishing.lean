-- Prove2me | solution 1 for vcdim_finite_imp_rademacher_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:21.116801+00:00
-- url     : https://prove2.me/submissions/882c4bf5-e9ae-41ad-8b01-4b782dfbdfbc

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_rademacherCorrelation_abs_le_one
public import Theorems.Thm_rademacherComplexity_le_one
public import Theorems.Thm_vcdim_bounds_rademacher_quantitative
section
@[expose] public section
universe u v
private theorem flipAt_involutive {m : ℕ} (i : Fin m) : Function.Involutive (flipAt i) := by
  intro σ; ext k; unfold flipAt
  simp_all
private theorem flipAt_boolToSign {m : ℕ} (i : Fin m) (σ : SignVector m) :
    boolToSign (flipAt i σ i) = -boolToSign (σ i) := by
  unfold flipAt; simp only [Function.update_self]
  unfold boolToSign; cases σ i <;> simp
private theorem flipAt_other {m : ℕ} (i : Fin m) (σ : SignVector m) (k : Fin m) (hk : k ≠ i) :
    flipAt i σ k = σ k := by
  unfold flipAt; simp [hk]
private theorem sum_boolToSign_cancel {m : ℕ} (i : Fin m) (f : SignVector m → ℝ)
    (hf : ∀ σ σ', (∀ k, k ≠ i → σ k = σ' k) → f σ = f σ') :
    ∑ σ : SignVector m, boolToSign (σ i) * f σ = 0 := by
  -- Use the involution flipAt i to show S = -S, hence S = 0.
  have hinv := flipAt_involutive i
  set g : SignVector m → ℝ := fun σ => boolToSign (σ i) * f σ
  -- Reindex: Σ g(σ) = Σ g(flipAt i σ) since flipAt i is a bijection.
  have h_eq : ∑ σ : SignVector m, g σ =
      ∑ σ : SignVector m, g (flipAt i σ) := by
    let e : SignVector m ≃ SignVector m := Equiv.ofBijective (flipAt i) hinv.bijective
    rw [show ∑ σ, g (flipAt i σ) = ∑ σ, g (e σ) from rfl]
    exact (Equiv.sum_comp e g).symm
  -- g(flipAt i σ) = -g(σ) since flipAt negates boolToSign at i but preserves f.
  have h_neg : ∀ σ, g (flipAt i σ) = -g σ := by
    intro σ
    change boolToSign (flipAt i σ i) * f (flipAt i σ) =
      -(boolToSign (σ i) * f σ)
    rw [flipAt_boolToSign, hf (flipAt i σ) σ (fun k hk => flipAt_other i σ k hk)]
    ring
  -- So S = Σ g(σ) = Σ -g(σ) = -S.
  have h_neg_sum : ∑ σ : SignVector m, g σ = -(∑ σ : SignVector m, g σ) := by
    conv_lhs => rw [h_eq]
    simp_rw [h_neg]
    simp [Finset.sum_neg_distrib]
  linarith
private theorem empRad_nonneg {X : Type u} (C : ConceptClass X Bool) {m : ℕ}
    (hm : m ≠ 0) (xs : Fin m → X) :
    0 ≤ EmpiricalRademacherComplexity X C xs := by
  unfold EmpiricalRademacherComplexity
  rw [dif_neg hm]
  apply mul_nonneg
  · apply div_nonneg one_pos.le; exact Nat.cast_nonneg _
  · by_cases hC : C.Nonempty
    · obtain ⟨h₀, hh₀⟩ := hC
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      have hbdd : ∀ σ, BddAbove { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } := by
        intro σ; refine ⟨1, fun r hr => ?_⟩
        obtain ⟨h', _, rfl⟩ := hr
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm_pos h' σ xs)
      have h_ge : ∀ σ : SignVector m,
          rademacherCorrelation h₀ σ xs ≤
            sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } :=
        fun σ => le_csSup_of_le (hbdd σ) ⟨h₀, hh₀, rfl⟩ le_rfl
      have h_sum_corr : ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs = 0 := by
        simp only [rademacherCorrelation, dif_neg hm]
        rw [← Finset.mul_sum, Finset.sum_comm]
        have : ∀ i : Fin m, ∑ σ : SignVector m,
            boolToSign (σ i) * boolToSign (h₀ (xs i)) = 0 :=
          fun i => sum_boolToSign_cancel i (fun _ => boolToSign (h₀ (xs i)))
            (fun _ _ _ => rfl)
        simp [this]
      calc (0 : ℝ) = ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs := h_sum_corr.symm
        _ ≤ ∑ σ : SignVector m,
              sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } :=
            Finset.sum_le_sum (fun σ _ => h_ge σ)
    · rw [Set.not_nonempty_iff_eq_empty] at hC
      simp_all
private theorem vcdim_zero_concepts_agree (X : Type u) (C : ConceptClass X Bool)
    (hd : VCDim X C = (0 : ℕ)) (h₁ h₂ : Concept X Bool) (hh₁ : h₁ ∈ C) (hh₂ : h₂ ∈ C)
    (x : X) : h₁ x = h₂ x := by
  by_contra hne
  -- {x} is shattered: we can realize both labelings via h₁ and h₂
  have hshat : Shatters X C {x} := by
    intro f
    -- f maps the unique element of {x} to some Bool value
    -- h₁ and h₂ disagree on x, so one of them matches f
    by_cases hf : f ⟨x, Finset.mem_singleton_self x⟩ = h₁ x
    · refine ⟨h₁, hh₁, fun ⟨y, hy⟩ => ?_⟩
      have hyx := Finset.mem_singleton.mp hy
      subst hyx; exact hf.symm
    · have hf2 : f ⟨x, Finset.mem_singleton_self x⟩ = h₂ x := by
        have : h₁ x ≠ h₂ x := hne
        cases hv1 : h₁ x <;> cases hv2 : h₂ x <;> simp_all
      refine ⟨h₂, hh₂, fun ⟨y, hy⟩ => ?_⟩
      have hyx := Finset.mem_singleton.mp hy
      subst hyx; exact hf2.symm
  -- But this gives VCDim ≥ 1, contradicting VCDim = 0
  have h1le : (1 : WithTop ℕ) ≤ VCDim X C := by
    unfold VCDim
    exact le_iSup₂_of_le {x} hshat (by simp)
  simp_all
private theorem vcdim_zero_rademacher_le_inv_sqrt (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (hd : VCDim X C = (0 : ℕ))
    (m : ℕ) (hm : 0 < m)
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi (fun _ : Fin m => D))] :
    RademacherComplexity X C D m ≤ 1 / Real.sqrt m := by
  -- Case split: C empty vs nonempty.
  by_cases hC : C.Nonempty
  · -- C nonempty: all concepts agree on each point (vcdim_zero_concepts_agree).
    -- So sSup over C collapses, and EmpRad reduces to a Rademacher average.
    -- Bound by 1/√m via Jensen: E[|Z|]² ≤ E[Z²] = 1/m for Z = avg of Rademacher RVs.
    suffices h_pw : ∀ xs : Fin m → X, EmpiricalRademacherComplexity X C xs ≤ 1 / Real.sqrt m by
      unfold RademacherComplexity
      calc ∫ xs, EmpiricalRademacherComplexity X C xs ∂(MeasureTheory.Measure.pi _)
          ≤ ∫ _xs, (1 / Real.sqrt m) ∂(MeasureTheory.Measure.pi (fun _ : Fin m => D)) := by
            apply MeasureTheory.integral_mono_of_nonneg
            · exact MeasureTheory.ae_of_all _
                (fun xs => empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs)
            · exact MeasureTheory.integrable_const _
            · exact MeasureTheory.ae_of_all _ h_pw
        _ = 1 / Real.sqrt m := by simp [MeasureTheory.integral_const]
    intro xs
    -- One-sided: all h ∈ C agree (VCDim=0), so sSup = corr(h₀). Then EmpRad = 0 by symmetry.
    obtain ⟨h₀, hh₀⟩ := hC
    have h_ssup_eq : ∀ σ : SignVector m,
        sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } =
          rademacherCorrelation h₀ σ xs := by
      intro σ
      have h_eq : { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } =
          {rademacherCorrelation h₀ σ xs} := by
        ext r; constructor
        · rintro ⟨h, hh, rfl⟩
          simp only [Set.mem_singleton_iff]
          unfold rademacherCorrelation; split
          · rfl
          · next hm' =>
            congr 1; apply Finset.sum_congr rfl; intro i _
            rw [vcdim_zero_concepts_agree X C hd h h₀ hh hh₀ (xs i)]
        · intro hr; rw [Set.mem_singleton_iff.mp hr]; exact ⟨h₀, hh₀, rfl⟩
      rw [h_eq, csSup_singleton]
    -- EmpRad = (1/N) Σ_σ corr(h₀,σ,xs) = 0 by Rademacher symmetry. 0 ≤ 1/√m.
    have h_emprad_zero : EmpiricalRademacherComplexity X C xs = 0 := by
      unfold EmpiricalRademacherComplexity
      rw [dif_neg (by omega)]
      simp_rw [h_ssup_eq]
      have : ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs = 0 := by
        simp only [rademacherCorrelation, dif_neg (by omega : ¬m = 0)]
        rw [← Finset.mul_sum, Finset.sum_comm]
        have : ∀ i : Fin m, ∑ σ : SignVector m,
            boolToSign (σ i) * boolToSign (h₀ (xs i)) = 0 :=
          fun i => sum_boolToSign_cancel i (fun _ => boolToSign (h₀ (xs i)))
            (fun _ _ _ => rfl)
        simp [this]
      rw [this, mul_zero]
    simp_all
  · -- C empty: EmpRad = 0 ≤ 1/√m.
    rw [Set.not_nonempty_iff_eq_empty] at hC
    have h_emp_zero : ∀ xs : Fin m → X, EmpiricalRademacherComplexity X C xs = 0 := by
      intro xs
      unfold EmpiricalRademacherComplexity
      simp_all
    unfold RademacherComplexity
    simp_all
private theorem analytical_log_sqrt_bound (d m : ℕ) (ε : ℝ)
    (hε : 0 < ε) (_hε1 : ε ≤ 1) (hd_pos : 0 < d) (hdm : d ≤ m)
    (hm_large : (Nat.ceil (32 * (↑d + 1) / ε ^ 4) + 1 : ℕ) ≤ m) :
    2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m < ε ^ 2 := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast Nat.lt_of_lt_of_le (by omega : 0 < d) hdm
  have hd_pos_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos
  have hdm_r : (d : ℝ) ≤ m := Nat.cast_le.mpr hdm
  -- t = m/d ≥ 1
  set t := (m : ℝ) / d with ht_def
  have ht_pos : 0 < t := div_pos hm_pos hd_pos_r
  have ht_ge_one : 1 ≤ t := by rw [ht_def]; rw [le_div_iff₀ hd_pos_r]; linarith
  -- Rewrite: 2d·log(em/d)/m = 2·log(et)/t
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h_rewrite : 2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m =
      2 * Real.log (Real.exp 1 * t) / t := by
    rw [ht_def]
    field_simp
  rw [h_rewrite]
  -- log(et) = 1 + log(t) ≤ 1 + 2√t (using log(t) ≤ 2√t for t ≥ 1)
  have het_pos : (0 : ℝ) < Real.exp 1 * t := by positivity
  have het_nonneg : (0 : ℝ) ≤ Real.exp 1 * t := le_of_lt het_pos
  -- Use log(et) ≤ 2√(et) via log_le_rpow_div
  have h_log_bound : Real.log (Real.exp 1 * t) ≤ 2 * Real.sqrt (Real.exp 1 * t) := by
    have h1 := Real.log_le_rpow_div het_nonneg (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : (Real.exp 1 * t) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) =
        2 * (Real.exp 1 * t) ^ (1 / 2 : ℝ) := by
      ring
    rw [h2] at h1
    rwa [Real.sqrt_eq_rpow]
  -- So 2·log(et)/t ≤ 4√(et)/t = 4√(e)/√t ≤ 4√3/√t (since e < 3)
  -- Actually we bound more directly: 4√e/√t < ε² when t > 48/ε⁴ (since 16e < 48)
  -- But we have t > 32/ε⁴, and e < 3, so 16e < 48 > 32... need to check.
  -- Actually: 2·log(et)/t ≤ 4·√(et)/t. And √(et)/t = √e/(√t).
  -- So 2·log(et)/t ≤ 4√e/√t.
  -- Need: 4√e/√t < ε², i.e., √t > 4√e/ε².
  -- From t > 32/ε⁴: √t > √(32)/ε² = 4√2/ε².
  -- Need: 4√2 ≥ 4√e, i.e., √2 ≥ √e, i.e., 2 ≥ e. FALSE (e ≈ 2.718).
  -- So we need a tighter bound. Use: e < 3, so √e < √3 < 2.
  -- 4√e/ε² < 4·2/ε² = 8/ε². Need √t > 8/ε², i.e., t > 64/ε⁴.
  -- But we only have t > 32/ε⁴. This is tight. Let's use a different approach.
  -- Use log(et) = 1 + log(t) and log(t) ≤ 2√t (from log_le_rpow_div).
  -- Then 2(1 + log(t))/t ≤ 2(1 + 2√t)/t = 2/t + 4/√t.
  -- For t ≥ 32/ε⁴: 2/t ≤ 2ε⁴/32 = ε⁴/16 ≤ ε²/16 (since ε ≤ 1).
  -- 4/√t ≤ 4ε²/√32 = 4ε²/(4√2) = ε²/√2 < ε².
  -- Total: ε²/16 + ε²/√2 < ε². ✓ (since 1 / 16 + 1/√2 < 1)
  have h_log_t_bound : Real.log t ≤ 2 * Real.sqrt t := by
    have h1 := Real.log_le_rpow_div (le_of_lt ht_pos) (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : t ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * t ^ (1 / 2 : ℝ) := by ring
    rw [h2] at h1
    rwa [Real.sqrt_eq_rpow]
  have h_log_et : Real.log (Real.exp 1 * t) = 1 + Real.log t := by
    rw [Real.log_mul (ne_of_gt he_pos) (ne_of_gt ht_pos), Real.log_exp]
  -- 2·log(et)/t = 2(1 + log t)/t = 2/t + 2·log(t)/t
  have h_split : 2 * Real.log (Real.exp 1 * t) / t = 2 / t + 2 * Real.log t / t := by
    rw [h_log_et]; ring
  rw [h_split]
  -- Bound each term separately
  -- Term 1: 2/t < ε²/2 (since t > 32/ε⁴ implies 2/t < 2ε⁴/32 = ε⁴/16 < ε²/2)
  -- Term 2: 2·log(t)/t ≤ 4/√t < ε²/2 (since √t > 4√2/ε² > 8/ε²... hmm)
  -- Let's just bound: 2/t + 4/√t < ε²
  have h_mid : 2 / t + 2 * Real.log t / t ≤ 2 / t + 4 / Real.sqrt t := by
    have : 2 * Real.log t / t ≤ 4 * Real.sqrt t / t := by
      apply div_le_div_of_nonneg_right _ (le_of_lt ht_pos)
      linarith only [h_log_t_bound]
    have h_sq : 4 * Real.sqrt t / t = 4 / Real.sqrt t := by
      rw [div_eq_div_iff (ne_of_gt ht_pos) (ne_of_gt (Real.sqrt_pos.mpr ht_pos))]
      -- Goal: 4 * √t * √t = 4 * t
      rw [show 4 * Real.sqrt t * Real.sqrt t = 4 * (Real.sqrt t * Real.sqrt t) by ring]
      rw [Real.mul_self_sqrt (le_of_lt ht_pos)]
    rw [h_sq] at this
    exact add_le_add (le_refl _) this
  -- Need: 2/t + 4/√t < ε².
  -- From t > 32/ε⁴: 2/t < ε⁴/16 and 4/√t < 4ε²/√32 = ε²/√2.
  -- Total < ε⁴/16 + ε²/√2 < ε² (since ε ≤ 1 and 1 / 16 + 1/√2 < 1).
  have hε4_pos : (0 : ℝ) < ε ^ 4 := by positivity
  have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
  have h_t_large : 32 / ε ^ 4 < t := by
    rw [ht_def, div_lt_div_iff₀ hε4_pos hd_pos_r]
    have hceil : (32 * (↑d + 1) / ε ^ 4 : ℝ) < m := by
      calc (32 * (↑d + 1) / ε ^ 4 : ℝ)
          ≤ ↑(⌈32 * (↑d + 1) / ε ^ 4⌉₊) := Nat.le_ceil _
        _ < (m : ℝ) := by exact_mod_cast (by omega : ⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊ < m)
    rw [div_lt_iff₀ hε4_pos] at hceil
    linarith only [hceil]
  -- Bound 4/√t: √t > 4√2/ε² (since t > 32/ε⁴), so 4/√t < ε²/√2
  have h_sqrt_t_lower : 4 * Real.sqrt 2 / ε ^ 2 < Real.sqrt t := by
    rw [Real.lt_sqrt (by positivity)]
    calc (4 * Real.sqrt 2 / ε ^ 2) ^ 2
        = 32 / ε ^ 4 := by
          rw [div_pow, mul_pow, sq (Real.sqrt 2), Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
          ring
      _ < t := h_t_large
  have h_4_over_sqrt : 4 / Real.sqrt t < ε ^ 2 / Real.sqrt 2 := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.mpr ht_pos) (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
    calc 4 * Real.sqrt 2 = ε ^ 2 * (4 * Real.sqrt 2 / ε ^ 2) := by field_simp
      _ < ε ^ 2 * Real.sqrt t :=
          mul_lt_mul_of_pos_left h_sqrt_t_lower hε2_pos
  -- Bound 2/t: t > 32/ε⁴ implies 2/t < ε⁴/16 ≤ ε²/16
  have h_2_over_t : 2 / t < ε ^ 2 / 16 := by
    rw [div_lt_div_iff₀ ht_pos (by norm_num : (0:ℝ) < 16)]
    -- Need: 2 * 16 = 32 < ε² * t
    -- From h_t_large: 32 / ε⁴ < t, so ε² * (32 / ε⁴) < ε² * t
    -- ε² * (32 / ε⁴) = 32 / ε², and 32 / ε² ≥ 32 (since ε² ≤ 1)
    have hε2_le : ε ^ 2 ≤ 1 := by nlinarith only [hε, _hε1]
    have h1 : ε ^ 2 * (32 / ε ^ 4) < ε ^ 2 * t :=
      mul_lt_mul_of_pos_left h_t_large hε2_pos
    have h2 : ε ^ 2 * (32 / ε ^ 4) = 32 / ε ^ 2 := by
      field_simp
    have h3 : (32 : ℝ) ≤ 32 / ε ^ 2 := by
      rw [le_div_iff₀ hε2_pos]
      linarith only [hε2_le]
    calc 2 * 16 = (32 : ℝ) := by norm_num
      _ ≤ 32 / ε ^ 2 := h3
      _ < ε ^ 2 * t := h2 ▸ h1
  -- ε²/16 + ε²/√2 < ε²: show 1 / 16 + 1/√2 < 1
  -- √2 > 4 / 3, so 1/√2 < 3 / 4, so 1 / 16 + 1/√2 < 1 / 16 + 3 / 4 = 13 / 16 < 1
  have h_sqrt2_bound : (4 : ℝ) / 3 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 4 / 3)]
    norm_num
  have h_inv_sqrt2 : ε ^ 2 / Real.sqrt 2 < 3 * ε ^ 2 / 4 := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)) (by norm_num : (0:ℝ) < 4)]
    calc ε ^ 2 * 4 = (3 * ε ^ 2) * (4 / 3) := by ring
      _ < (3 * ε ^ 2) * Real.sqrt 2 :=
        mul_lt_mul_of_pos_left h_sqrt2_bound (by positivity)
  -- Combine: 2/t + 4/√t < ε²/16 + ε²/√2 < ε²/16 + 3ε²/4 = 13ε²/16 < ε²
  linarith only [h_mid, h_2_over_t, h_4_over_sqrt, h_inv_sqrt2, hε2_pos]
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hvcdim : VCDim X C < ⊤) :
    ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε := by
  rw [WithTop.lt_top_iff_ne_top] at hvcdim
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hvcdim
  intro ε hε
  -- For ε > 1: Rad ≤ 1 < ε.
  by_cases hε1 : 1 < ε
  · use 1; intro D hD m hm
    have : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi (fun _ : Fin m => D)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    exact lt_of_le_of_lt (rademacherComplexity_le_one X C D m (by omega)) hε1
  · push Not at hε1
    -- ε ≤ 1: use VCDim bound. For d > 0, Rad ≤ √(2d·log(em/d)/m) < ε for large m.
    -- For d = 0: Rad ≤ 1/√m < ε for large m (Khintchine).
    -- The analytical chain: 2d·log(em/d)/m → 0 as m → ∞.
    -- Pick m₀ = max(d+1, ⌈32(d+1)/ε⁴⌉ + 1).
    use max (d + 1) (Nat.ceil (32 * (↑d + 1) / ε ^ 4) + 1)
    intro D hD m hm
    have hm_pos : 0 < m := by omega
    have : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi (fun _ : Fin m => D)) :=
      MeasureTheory.Measure.pi.instIsProbabilityMeasure _
    by_cases hd_pos : d = 0
    · -- d = 0: use Khintchine bound Rad ≤ 1/√m < ε for large m.
      have hd0 : VCDim X C = (0 : ℕ) := by rw [← hd]; subst hd_pos; rfl
      have h_bound := vcdim_zero_rademacher_le_inv_sqrt X C D hd0 m hm_pos
      calc RademacherComplexity X C D m
          ≤ 1 / Real.sqrt m := h_bound
        _ < ε := by
          rw [div_lt_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm_pos))]
          -- Need: 1 < ε · √m. Suffices: 1/ε² < m.
          -- m ≥ ⌈32/ε⁴⌉+1 > 32/ε⁴ ≥ 1/ε² (since ε ≤ 1).
          have hm_ge : (⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊ + 1 : ℕ) ≤ m := by omega
          have h_ceil_le_m : (32 * ((d : ℝ) + 1) / ε ^ 4 : ℝ) < m := by
            calc (32 * ((d : ℝ) + 1) / ε ^ 4 : ℝ)
                ≤ ↑(⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊) := Nat.le_ceil _
              _ < (m : ℝ) := by exact_mod_cast (by omega : ⌈32 * ((d : ℝ) + 1) / ε ^ 4⌉₊ < m)
          subst hd_pos; simp only [Nat.cast_zero, zero_add, mul_one] at h_ceil_le_m
          -- 32/ε⁴ < m. Need: 1 < ε·√m.
          -- 1/ε² ≤ 32/ε⁴ < m (since ε ≤ 1 ⟹ 1/ε² ≤ 32/ε⁴).
          -- So m > 1/ε², hence √m > 1/ε, hence ε·√m > 1.
          have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
          have h_inv_eps2_lt_m : 1 / ε ^ 2 < (m : ℝ) := by
            have : 1 / ε ^ 2 ≤ 32 / ε ^ 4 := by
              rw [div_le_div_iff₀ hε2_pos (by positivity)]
              -- Need: ε⁴ ≤ 32·ε², i.e., ε² ≤ 32. True since ε ≤ 1.
              have : ε ^ 2 ≤ 1 := by nlinarith
              nlinarith
            linarith
          -- √m > 1/ε, so ε·√m > 1
          have h_sqrt_m : 1 / ε < Real.sqrt m := by
            rw [Real.lt_sqrt (by positivity)]
            simp_all
          -- ε * (1/ε) = 1, and ε * √m > ε * (1/ε) = 1
          have : ε * (1 / ε) = 1 := by field_simp
          nlinarith [mul_lt_mul_of_pos_left h_sqrt_m hε]
    · -- d > 0: Rad ≤ √(2d·log(em/d)/m) < ε.
      have hd_pos' : 0 < d := Nat.pos_of_ne_zero hd_pos
      have hdm : d ≤ m := by omega
      have h_quant := vcdim_bounds_rademacher_quantitative X C D m hm_pos d hd.symm hd_pos' hdm
      have h_anal := analytical_log_sqrt_bound d m ε hε hε1 hd_pos' hdm (by omega)
      calc RademacherComplexity X C D m
          ≤ Real.sqrt (2 * ↑d * Real.log (Real.exp 1 * ↑m / ↑d) / ↑m) := h_quant
        _ < Real.sqrt (ε ^ 2) := by
            apply Real.sqrt_lt_sqrt
            · apply div_nonneg
              · apply mul_nonneg
                · simp_all
                · exact Real.log_nonneg (by
                    rw [le_div_iff₀ (Nat.cast_pos.mpr hd_pos')]
                    have hd_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd_pos'
                    have hm_r : (d : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hdm
                    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
                    nlinarith [Real.add_one_le_exp (1 : ℝ)])
              · exact Nat.cast_nonneg m
            · exact h_anal
        _ = ε := by rw [Real.sqrt_sq (le_of_lt hε)]
