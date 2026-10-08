-- Prove2me | solution 1 for logDeriv_intervalIntegral_eq_two_pi_I_of_im_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T19:07:38.442863+00:00
-- url     : https://prove2.me/submissions/b3a421b2-be23-4653-a19e-6e107b71c1d0

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped ContDiff
open Complex MeasureTheory Set

/-!
# Winding numbers of `C¹` loops in `ℂ \ {0}` via the logarithmic derivative
-/


noncomputable section

namespace WindA

/-- The log-derivative primitive recovers the loop: `c t = c 0 · exp (∫₀ᵗ c'/c)`. -/
lemma eq_mul_exp_integral {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (t : ℝ) :
    c t = c 0 * exp (∫ s in (0 : ℝ)..t, c' s / c s) := by
  have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
  have hq : Continuous fun s => c' s / c s := hc'.div hcc hne
  set L : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, c' s / c s
  have hL : ∀ t, HasDerivAt L (c' t / c t) t := fun t =>
    (hq.integral_hasStrictDerivAt 0 t).hasDerivAt
  set g : ℝ → ℂ := fun t => c t * exp (-L t)
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h1 : HasDerivAt g (c' t * exp (-L t) + c t * (exp (-L t) * -(c' t / c t))) t :=
      (hc t).mul (HasDerivAt.cexp (f := fun t => -L t) (hL t).neg)
    convert h1 using 1
    field_simp [hne t]
    ring
  have hconst : ∀ t, g t = g 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0
  have hL0 : L 0 = 0 := by simp [L]
  have := hconst t
  simp only [g, hL0, neg_zero, Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- The log-derivative integral of a closed `C¹` loop lies in `2πi ℤ`. -/
lemma integral_mem_two_pi_I {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (hper : c 1 = c 0) :
    ∃ k : ℤ, ∫ s in (0 : ℝ)..1, c' s / c s = k * (2 * Real.pi * I) := by
  have h := eq_mul_exp_integral hc hc' hne 1
  rw [hper] at h
  have h1 : exp (∫ s in (0 : ℝ)..1, c' s / c s) = 1 := by
    have h0 := hne 0
    exact mul_left_cancel₀ h0 (h.symm.trans (mul_one _).symm)
  exact Complex.exp_eq_one_iff.1 h1

lemma im_integral {f : ℝ → ℂ} (hf : Continuous f) (a b : ℝ) :
    (∫ s in a..b, f s).im = ∫ s in a..b, (f s).im :=
  (Complex.imCLM.intervalIntegral_comp_comm (hf.intervalIntegrable a b)).symm

/-- Homotopy invariance of the log-derivative integral. -/
lemma integral_eq_of_homotopy {F F' : ℝ → ℝ → ℂ}
    (hF : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, HasDerivAt (F r) (F' r s) s)
    (hcF : ContinuousOn (Function.uncurry F) (Icc 0 1 ×ˢ univ))
    (hcF' : ContinuousOn (Function.uncurry F') (Icc 0 1 ×ˢ univ))
    (hne : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, F r s ≠ 0)
    (hper : ∀ r ∈ Icc (0 : ℝ) 1, F r 1 = F r 0) :
    ∫ s in (0 : ℝ)..1, F' 1 s / F 1 s = ∫ s in (0 : ℝ)..1, F' 0 s / F 0 s := by
  set p : ℝ → ℝ := fun r => (projIcc (0 : ℝ) 1 zero_le_one r : ℝ)
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpI : ∀ r, p r ∈ Icc (0 : ℝ) 1 := fun r => (projIcc (0 : ℝ) 1 zero_le_one r).2
  have hpid : ∀ r ∈ Icc (0 : ℝ) 1, p r = r := fun r hr => by simp [p, projIcc_of_mem _ hr]
  set G : ℝ → ℝ → ℂ := fun r s => F' (p r) s / F (p r) s
  have hmap : Continuous fun q : ℝ × ℝ => (p q.1, q.2) := (hp.comp continuous_fst).prodMk continuous_snd
  have hmapI : ∀ q : ℝ × ℝ, (p q.1, q.2) ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) :=
    fun q => ⟨hpI q.1, trivial⟩
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous fun q : ℝ × ℝ => Function.uncurry F' (p q.1, q.2) :=
      hcF'.comp_continuous hmap hmapI
    have h2 : Continuous fun q : ℝ × ℝ => Function.uncurry F (p q.1, q.2) :=
      hcF.comp_continuous hmap hmapI
    exact h1.div h2 fun q => hne _ (hpI q.1) q.2
  set W : ℝ → ℂ := fun r => ∫ s in (0 : ℝ)..1, G r s
  have hW : Continuous W := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hGc 0 1
  -- `W r ∈ 2πiℤ`
  have hk : ∀ r, ∃ k : ℤ, W r = k * (2 * Real.pi * I) := by
    intro r
    have hr := hpI r
    have hcont : Continuous (F' (p r)) := by
      have := hGc.comp (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (r, s))
      have h1 : Continuous fun s : ℝ => Function.uncurry F' (p r, s) :=
        hcF'.comp_continuous (continuous_const.prodMk continuous_id) fun s => ⟨hr, trivial⟩
      exact h1
    exact integral_mem_two_pi_I (hF _ hr) hcont (hne _ hr) (hper _ hr)
  set f : ℝ → ℝ := fun r => (W r).im / (2 * Real.pi)
  have hf : Continuous f := (Complex.continuous_im.comp hW).div_const _
  have hfint : ∀ r, ∃ k : ℤ, f r = k := by
    intro r; obtain ⟨k, hk⟩ := hk r
    refine ⟨k, ?_⟩
    simp only [f, hk]
    simp [Complex.mul_im]
  have hWre : ∀ r, W r = (f r : ℂ) * (2 * Real.pi * I) := by
    intro r; obtain ⟨k, hk'⟩ := hk r
    have : f r = k := by
      simp only [f, hk']; simp [Complex.mul_im]
    rw [this, hk']; push_cast; ring
  -- `f` is constant on `[0, 1]`
  obtain ⟨k0, hk0⟩ := hfint 0
  obtain ⟨k1, hk1⟩ := hfint 1
  have hk01 : k0 = k1 := by
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · have hmem : (k0 : ℝ) + 1 / 2 ∈ Icc (f 0) (f 1) := by
        rw [hk0, hk1]
        have : (k0 : ℝ) + 1 ≤ k1 := by exact_mod_cast h
        constructor <;> linarith
      obtain ⟨r, -, hr⟩ := intermediate_value_Icc zero_le_one hf.continuousOn hmem
      obtain ⟨k, hk⟩ := hfint r
      rw [hk] at hr
      have h1 : (k : ℝ) - k0 = 1 / 2 := by linarith
      have h2 : ((k - k0 : ℤ) : ℝ) = 1 / 2 := by push_cast; exact h1
      have h3 : (2 : ℝ) * ((k - k0 : ℤ) : ℝ) = 1 := by rw [h2]; norm_num
      have h4 : (2 * (k - k0) : ℤ) = 1 := by exact_mod_cast h3
      omega
    · have hmem : (k1 : ℝ) + 1 / 2 ∈ Icc (f 1) (f 0) := by
        rw [hk0, hk1]
        have : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast h
        constructor <;> linarith
      obtain ⟨r, -, hr⟩ := intermediate_value_Icc' zero_le_one hf.continuousOn hmem
      obtain ⟨k, hk⟩ := hfint r
      rw [hk] at hr
      have h1 : (k : ℝ) - k1 = 1 / 2 := by linarith
      have h2 : ((k - k1 : ℤ) : ℝ) = 1 / 2 := by push_cast; exact h1
      have h3 : (2 : ℝ) * ((k - k1 : ℤ) : ℝ) = 1 := by rw [h2]; norm_num
      have h4 : (2 * (k - k1) : ℤ) = 1 := by exact_mod_cast h3
      omega
  have hW1 : W 1 = W 0 := by rw [hWre 1, hWre 0, hk0, hk1, hk01]
  have e1 : W 1 = ∫ s in (0 : ℝ)..1, F' 1 s / F 1 s := by
    simp only [W, G, hpid 1 ⟨zero_le_one, le_rfl⟩]
  have e0 : W 0 = ∫ s in (0 : ℝ)..1, F' 0 s / F 0 s := by
    simp only [W, G, hpid 0 ⟨le_rfl, zero_le_one⟩]
  rw [← e1, ← e0, hW1]

/-- A closed loop whose argument strictly increases and which returns to the ray of
`c 0` only at the ends winds exactly once. -/
lemma integral_eq_two_pi_I_of_im_pos {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (hper : c 1 = c 0)
    (hpos : ∀ t, 0 < (c' t / c t).im)
    (hray : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ l : ℝ, 0 < l → c t ≠ (l : ℂ) * c 0) :
    ∫ s in (0 : ℝ)..1, c' s / c s = 2 * Real.pi * I := by
  have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
  have hq : Continuous fun s => c' s / c s := hc'.div hcc hne
  obtain ⟨k, hk⟩ := integral_mem_two_pi_I hc hc' hne hper
  set θ : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, c' s / c s).im
  have hθ : ∀ t, θ t = ∫ s in (0 : ℝ)..t, (c' s / c s).im := fun t => im_integral hq 0 t
  have hθc : Continuous θ := by
    have : θ = fun t => ∫ s in (0 : ℝ)..t, (c' s / c s).im := funext hθ
    rw [this]
    exact continuous_iff_continuousAt.2 fun t =>
      ((Complex.continuous_im.comp hq).integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  have hθ1 : θ 1 = 2 * Real.pi * k := by
    simp only [θ, hk]; simp [Complex.mul_im]; ring
  have hθ1pos : 0 < θ 1 := by
    rw [hθ]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Complex.continuous_im.comp hq).intervalIntegrable 0 1) (fun t _ => hpos t) zero_lt_one
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := by
      rw [hθ1] at hθ1pos
      have := Real.pi_pos
      nlinarith
    exact_mod_cast this
  have hk1 : k = 1 := by
    by_contra hk1
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show (2 : ℤ) ≤ k by omega)
    have hθ0 : θ 0 = 0 := by simp [θ]
    have hmem : 2 * Real.pi ∈ Icc (θ 0) (θ 1) := by
      rw [hθ0, hθ1]
      have := Real.pi_pos
      constructor <;> nlinarith
    obtain ⟨t, ht, hθt⟩ := intermediate_value_Icc zero_le_one hθc.continuousOn hmem
    have ht0 : t ≠ 0 := by
      rintro rfl; rw [hθ0] at hθt; have := Real.pi_pos; linarith
    have ht1 : t ≠ 1 := by
      rintro rfl; rw [hθ1] at hθt; have := Real.pi_pos; nlinarith
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    set L := ∫ s in (0 : ℝ)..t, c' s / c s
    have hL : L = (L.re : ℂ) + (2 * Real.pi : ℝ) * I := by
      apply Complex.ext <;> simp [θ] at hθt ⊢
      first | exact hθt | exact hθt.symm
    have hct := eq_mul_exp_integral hc hc' hne t
    apply hray t htI (Real.exp L.re) (Real.exp_pos _)
    have h2 : exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
      push_cast; exact Complex.exp_two_pi_mul_I
    have hE : exp L = (Real.exp L.re : ℂ) := by
      conv_lhs => rw [hL]
      rw [Complex.exp_add, h2, mul_one, Complex.ofReal_exp]
    rw [hct, hE]; ring
  rw [hk, hk1]; simp

end WindA

theorem solution {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (hper : c 1 = c 0)
    (hpos : ∀ t, 0 < (c' t / c t).im)
    (hray : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ l : ℝ, 0 < l → c t ≠ (l : ℂ) * c 0) :
    ∫ s in (0 : ℝ)..1, c' s / c s = 2 * Real.pi * Complex.I :=
  WindA.integral_eq_two_pi_I_of_im_pos hc hc' hne hper hpos hray
