-- Prove2me | solution 49 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:09.082062+00:00
-- url     : https://prove2.me/submissions/86018da8-b0dc-4ae1-8069-e42c5858ae6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_fourth_power_prime_ramp_upper_windows
import Theorems.Thm_MasulloRH_prime_ramp_chord_and_fourth_power_bound
import Theorems.Thm_XiPairingPublished_concrete_xi_no_real_zeros
import Theorems.Thm_EtaQBridgePublished_concrete_xi_bridge
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

-- Step 1: `MasulloRH.fourth_power_prime_ramp_upper_windows` implies `MasulloRH.smoothed_prime_ramp_upper_windows` (accepted reduction of `MasulloRH.smoothed_prime_ramp_upper_windows`).
section

open Finset ArithmeticFunction MasulloRH

theorem MasulloRH.smoothed_prime_ramp_upper_windows :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ X : ℝ, 1 ≤ X → ∃ Y : ℝ, X ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
        (∑ n ∈ Finset.range (⌊y⌋₊ + 1),
          ArithmeticFunction.vonMangoldt n * max (y / (n : ℝ) - 1) 0) -
          y * (Real.log y - 1 - Real.eulerMascheroniConstant) ≤ C * y ^ θ := by
  intro θ hhalf hone
  obtain ⟨δ,C,hδ,hC,hdisc⟩ := fourth_power_prime_ramp_upper_windows θ hhalf hone
  refine ⟨δ,C+225/4,hδ,by positivity,fun X hX => ?_⟩
  let m := max 1 ⌈X⌉₊
  obtain ⟨K,hK,h⟩ := hdisc m (le_max_left ..)
  have hK1 : 1 ≤ K := (show 1 ≤ m from le_max_left ..).trans hK
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK1
  have hXK : X ≤ K := (Nat.le_ceil X).trans (by exact_mod_cast (show ⌈X⌉₊ ≤ m from le_max_right ..).trans hK)
  have hY : X ≤ (K:ℝ)^4 := hXK.trans (le_self_pow₀ hK' (by norm_num))
  refine ⟨(K:ℝ)^4,hY,fun y hy => ?_⟩
  have hy0 : 0 ≤ y := (pow_nonneg (Nat.cast_nonneg K) _).trans hy.1
  let r := y ^ ((4:ℝ)⁻¹)
  have hr : 0 ≤ r := Real.rpow_nonneg hy0 _
  have hr4 : r^4=y := Real.rpow_inv_natCast_pow hy0 (by decide : (4:ℕ)≠0)
  let k := ⌊r⌋₊
  have hkR : (k:ℝ)≤r := Nat.floor_le hr
  have hrk : r < (k:ℝ)+1 := Nat.lt_floor_add_one r
  have hKk : K≤k := Nat.le_floor <| le_of_pow_le_pow_left₀ (by decide : (4:ℕ)≠0) hr (hr4.symm ▸ hy.1)
  have hpow : ((K:ℝ)^4)^(1+δ) = ((K:ℝ)^(1+δ))^4 := by
    rw [←Real.rpow_natCast_mul (Nat.cast_nonneg K),←Real.rpow_mul_natCast (Nat.cast_nonneg K)]
    congr 1;ring
  have htop : r ≤ (K:ℝ)^(1+δ) := le_of_pow_le_pow_left₀ (by decide : (4:ℕ)≠0) (by positivity) (hr4 ▸ (hy.2.trans_eq hpow))
  have hkr := hkR.trans htop
  have hnext : ((k+1:ℕ):ℝ) ≤ (K:ℝ)^(1+δ)+1 := by push_cast; linarith
  have hright := h (k+1) (hKk.trans (Nat.le_succ k)) hnext
  push_cast at hright
  apply prime_ramp_chord_and_fourth_power_bound.2 k (hK1.trans hKk) θ C hhalf.le hone.le hC (h k hKk (by linarith only [hkr])) hright
  · exact (pow_le_pow_left₀ (Nat.cast_nonneg k) hkR 4).trans_eq hr4
  · exact hr4 ▸ pow_le_pow_left₀ hr hrk.le 4

end

-- Step 2: `MasulloRH.smoothed_prime_ramp_upper_windows` implies `MasulloRH.zero_free_right` (accepted reduction of `MasulloRH.zero_free_right`).
section

/-!
# A one-sided prime-ramp reduction of the rational zero-free target

The proof constructs its own gamma moment estimates, comparison of
Taylor coefficients with exponential moments, pole detection and Mellin
computation for the corrected von Mangoldt ramp. The arithmetical
hypothesis is the open upper bound on relative scale intervals.

The source motivating this reduction is the analytic endpoint of
Levent Alpöge's 20 November 2026 Lean release, especially
Deduction.zeroFree_of_rpow_window. <https://alpo.ge/remark.pdf>
-/

set_option autoImplicit false

open Real Set Filter MeasureTheory Topology

namespace MasulloAlpoge

/-- Normalized exponential moment on the positive half-line. -/
noncomputable def gammaMoment (a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  u^n * Real.exp (-(a*u)) / (n.factorial : ℝ)

theorem gammaMoment_nonneg (a : ℝ) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ gammaMoment a n u := by
  unfold gammaMoment
  positivity

theorem gammaMoment_integrable {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntegrableOn (gammaMoment a n) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) zero_lt_one ha
  unfold gammaMoment
  simpa only [IntegrableOn, Real.rpow_one, Real.rpow_natCast, neg_mul] using
    h.div_const (n.factorial : ℝ)

private theorem gammaMoment_mass {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ u in Ioi (0:ℝ), gammaMoment a n u) = 1/a^(n+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1) (by positivity) ha
  simp only [Real.Gamma_nat_eq_factorial, add_sub_cancel_right, Real.rpow_natCast] at h
  have hp : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hcast : (n:ℝ)+1 = ((n+1:ℕ):ℝ) := by simp
  rw [hcast] at h
  simp only [Real.rpow_natCast] at h
  simp [gammaMoment, integral_div, h, one_div, inv_pow, hp.ne']

theorem exp_mul_gammaMoment (a r : ℝ) (n : ℕ) (u : ℝ) :
    Real.exp (r*u) * gammaMoment a n u = gammaMoment (a-r) n u := by
  unfold gammaMoment
  calc
    _ = u^n * (Real.exp (r*u) * Real.exp (-(a*u))) / (n.factorial : ℝ) := by ring
    _ = _ := by rw [← Real.exp_add, show r*u+(-(a*u)) = -((a-r)*u) by ring]

/-- Two exponential tilts control the moments outside a scale interval. -/
theorem gammaMoment_tail_le {a r U V : ℝ} (hr : 0 < r) (ha : r < a) (n : ℕ) :
    (∫ u in Ioi (0:ℝ) \ Icc U V, gammaMoment a n u) ≤
      Real.exp (r*U)/(a+r)^(n+1) + Real.exp (-r*V)/(a-r)^(n+1) := by
  let S := Ioi (0:ℝ) \ Icc U V
  let F (u : ℝ) := Real.exp (r*U)*gammaMoment (a+r) n u +
    Real.exp (-r*V)*gammaMoment (a-r) n u
  have hai : 0 < a := hr.trans ha
  have hap : 0 < a+r := by positivity
  have ham : 0 < a-r := sub_pos.mpr ha
  have hl := (gammaMoment_integrable hap n).const_mul (Real.exp (r*U))
  have hR := (gammaMoment_integrable ham n).const_mul (Real.exp (-r*V))
  have hi : IntegrableOn F (Ioi 0) := hl.add hR
  have hF {u : ℝ} (hu : 0 ≤ u) : 0 ≤ F u := by
    exact add_nonneg (mul_nonneg (Real.exp_nonneg _) (gammaMoment_nonneg _ _ hu))
      (mul_nonneg (Real.exp_nonneg _) (gammaMoment_nonneg _ _ hu))
  have hs : MeasurableSet S := measurableSet_Ioi.diff measurableSet_Icc
  have hsub : S ⊆ Ioi 0 := sdiff_subset
  refine (setIntegral_mono_on ((gammaMoment_integrable hai n).mono_set hsub)
    (hi.mono_set hsub) hs ?_).trans ?_
  · intro u hu
    have hpos : 0 ≤ u := (hsub hu).le
    have hw := gammaMoment_nonneg a n hpos
    by_cases h : u < U
    · have hE : 1 ≤ Real.exp (r*(U-u)) := Real.one_le_exp (by positivity)
      calc
        _ ≤ Real.exp (r*(U-u))*gammaMoment a n u := le_mul_of_one_le_left hw hE
        _ = Real.exp (r*U)*gammaMoment (a+r) n u := by
          rw [show r*(U-u) = r*U+(-r)*u by ring, Real.exp_add, mul_assoc, exp_mul_gammaMoment]
          rw [sub_neg_eq_add]
        _ ≤ F u := le_add_of_nonneg_right (mul_nonneg (Real.exp_nonneg _) (gammaMoment_nonneg _ _ hpos))
    · have h' : V < u := lt_of_not_ge (fun hn => hu.2 ⟨le_of_not_gt h,hn⟩)
      have hE : 1 ≤ Real.exp (r*(u-V)) := Real.one_le_exp (by positivity)
      calc
        _ ≤ Real.exp (r*(u-V))*gammaMoment a n u := le_mul_of_one_le_left hw hE
        _ = Real.exp (-r*V)*gammaMoment (a-r) n u := by
          rw [show r*(u-V) = -r*V + r*u by ring, Real.exp_add, mul_assoc, exp_mul_gammaMoment]
        _ ≤ F u := le_add_of_nonneg_left (mul_nonneg (Real.exp_nonneg _) (gammaMoment_nonneg _ _ hpos))
  · have hnon : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi 0)] F :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => hF hu.le)
    refine (setIntegral_mono_set hi hnon (Eventually.of_forall hsub)).trans_eq ?_
    unfold F
    rw [integral_add hl hR, integral_const_mul, integral_const_mul, gammaMoment_mass hap,
      gammaMoment_mass ham]
    ring

private theorem gammaMoment_tail_div_pow {a r U V b : ℝ} (hr : 0 < r) (ha : r < a)
    (hb : 0 < b) (n : ℕ)
    (hL : r*U ≤ (n:ℝ) * Real.log ((a+r)/b))
    (hR : -r*V + (n:ℝ) * Real.log (b/(a-r)) ≤ Real.log (b/(a-r))) :
    (∫ u in Ioi (0:ℝ) \ Icc U V, gammaMoment a n u) ≤
      ((a+r)⁻¹ + (b/(a-r))/(a-r)) / b^n := by
  have ha₀ : 0 < a := hr.trans ha
  have hp : 0 < a+r := by positivity
  have hm : 0 < a-r := sub_pos.mpr ha
  have hleL := Real.exp_le_exp.mpr hL
  rw [Real.exp_nat_mul, Real.exp_log (div_pos hp hb)] at hleL
  have hleR := Real.exp_le_exp.mpr hR
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (div_pos hb hm)] at hleR
  have h₁ : Real.exp (r*U)/(a+r)^(n+1) ≤ (a+r)⁻¹ / b^n := by
    calc
      _ ≤ ((a+r)/b)^n/(a+r)^(n+1) :=
        div_le_div_of_nonneg_right hleL (by positivity)
      _ = _ := by
        rw [div_pow, pow_succ]
        field_simp [hp.ne', hb.ne']
  have h₂ : Real.exp (-r*V)/(a-r)^(n+1) ≤ (b/(a-r))/(a-r)/b^n := by
    calc
      _ = (Real.exp (-r*V)*(b/(a-r))^n)/(a-r)/b^n := by
        rw [div_pow, pow_succ]
        field_simp [hm.ne', hb.ne']
      _ ≤ _ := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hleR hm.le) (by positivity)
  exact (gammaMoment_tail_le hr ha n).trans (by rw [add_div]; exact add_le_add h₁ h₂)

private theorem log_tilt_lower (τ : ℝ) (hτ : 0 < τ) :
    τ/(1+τ) ≤ Real.log (1+τ) := by
  have hp : 0 < 1+τ := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hp
  have he : τ/(1+τ) = 1-(1+τ)⁻¹ := by field_simp; ring
  exact he ▸ h

private theorem log_tilt_upper (τ : ℝ) (hτ : τ < 1) :
    -Real.log (1-τ) ≤ τ/(1-τ) := by
  have hp : 0 < 1-τ := sub_pos.mpr hτ
  have h := Real.one_sub_inv_le_log_of_pos hp
  have he : (1-τ)⁻¹-1 = τ/(1-τ) := by field_simp; ring
  rw [← he]
  linarith

/-- For every relative window length and every fixed rate increment, a large
enough base rate admits a moment whose two tilted tails have the stronger
rate. The order is the ceiling of the base rate times the window midpoint. -/
theorem gammaMoment_localization (δ D : ℝ) (hδ : 0 < δ) (hD : 0 ≤ D) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℝ, A ≤ a →
      ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U → ∃ n : ℕ, U ≤ (n:ℝ) ∧
        (∫ u in Ioi (0:ℝ) \ Icc U ((1+δ)*U), gammaMoment a n u) ≤ C/(a+D)^n := by
  let τ := δ/(4*(1+δ))
  let mid := 1+δ/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hmid : 1 ≤ mid := by dsimp [mid]; linarith
  have hmid₀ : 0 < mid := zero_lt_one.trans_le hmid
  have hτe : (1+δ)*τ = δ/4 := by
    dsimp [τ]
    have h₁ : 1+δ ≠ 0 := by positivity
    field_simp [h₁]
  have hτpos : τ < 1 := by
    dsimp [τ]
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hτlt : τ < δ/2 := by
    dsimp [τ]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg δ]
  let mL := mid*(τ/(1+τ))-τ
  let mR := τ*(1+δ)-mid*(τ/(1-τ))
  have hmL : 0 < mL := by
    dsimp [mL]
    rw [sub_pos, ← mul_div_assoc, lt_div_iff₀ (by positivity)]
    have h : 1+τ < mid := by dsimp [mid]; linarith
    simpa only [mul_comm] using mul_lt_mul_of_pos_left h hτ
  have hmR : 0 < mR := by
    dsimp [mR]
    rw [sub_pos, ← mul_div_assoc, div_lt_iff₀ (sub_pos.mpr hτpos)]
    have h : mid < (1+δ)*(1-τ) := by dsimp [mid]; nlinarith
    calc
      mid*τ < ((1+δ)*(1-τ))*τ := mul_lt_mul_of_pos_right h hτ
      _ = _ := by ring
  let A := max 1 (max (mid*D/mL) (mid*D/mR))
  refine ⟨A, zero_lt_one.trans_le (le_max_left _ _), fun a ha => ?_⟩
  have ha₁ : 1 ≤ a := (le_max_left _ _).trans ha
  have ha₀ : 0 < a := zero_lt_one.trans_le ha₁
  have hLa : mid*D/mL ≤ a := ((le_max_left _ _).trans (le_max_right _ _)).trans ha
  have hRa : mid*D/mR ≤ a := ((le_max_right _ _).trans (le_max_right _ _)).trans ha
  have hsmallL : mid*(D/a) ≤ mL := by
    rw [← mul_div_assoc, div_le_iff₀ ha₀]
    simpa only [mul_comm mL] using (div_le_iff₀ hmL).mp hLa
  have hsmallR : mid*(D/a) ≤ mR := by
    rw [← mul_div_assoc, div_le_iff₀ ha₀]
    simpa only [mul_comm mR] using (div_le_iff₀ hmR).mp hRa
  let r := τ*a
  let b := a+D
  have hr : 0 < r := mul_pos hτ ha₀
  have hra : r < a := by
    dsimp [r]
    simpa using mul_lt_mul_of_pos_right hτpos ha₀
  have hb : 0 < b := by dsimp [b]; positivity
  let qL := (a+r)/b
  let qR := b/(a-r)
  have hp : 0 < a+r := by positivity
  have hm : 0 < a-r := sub_pos.mpr hra
  have hqL : 0 < qL := div_pos hp hb
  have hqR : 0 < qR := div_pos hb hm
  have hqR₁ : 1 ≤ qR := by
    dsimp [qR, b]
    exact (le_div_iff₀ hm).mpr (by linarith)
  have hp₁ : 0 < 1+(D/a) := by positivity
  have hp₂ : 0 < 1+τ := by positivity
  have hp₃ : 0 < 1-τ := sub_pos.mpr hτpos
  have hlL : Real.log qL = Real.log (1+τ) - Real.log (1+D/a) := by
    have e : qL = (1+τ)/(1+D/a) := by
      dsimp [qL,r,b]
      field_simp [ha₀.ne', show a+D ≠ 0 by positivity]
    rw [e, Real.log_div hp₂.ne' hp₁.ne']
  have hlR : Real.log qR = Real.log (1+D/a) - Real.log (1-τ) := by
    have e : qR = (1+D/a)/(1-τ) := by
      dsimp [qR,r,b]
      have hne : a-τ*a ≠ 0 := hm.ne'
      field_simp [ha₀.ne', hp₃.ne', hne]
    rw [e, Real.log_div hp₁.ne' hp₃.ne']
  have hlogD : Real.log (1+D/a) ≤ D/a := by
    have h := Real.log_le_sub_one_of_pos hp₁
    linarith
  have hL : τ ≤ mid*Real.log qL := by
    rw [hlL, mul_sub]
    have h := mul_le_mul_of_nonneg_left (log_tilt_lower τ hτ) hmid₀.le
    have hD' := mul_le_mul_of_nonneg_left hlogD hmid₀.le
    dsimp [mL] at hsmallL
    linarith
  have hR : mid*Real.log qR ≤ τ*(1+δ) := by
    rw [hlR, mul_sub]
    have h := mul_le_mul_of_nonneg_left (log_tilt_upper τ hτpos) hmid₀.le
    have hD' := mul_le_mul_of_nonneg_left hlogD hmid₀.le
    dsimp [mR] at hsmallR
    linarith
  have hL₀ : 0 ≤ Real.log qL := by
    by_contra! h
    exact (not_le_of_gt (mul_neg_of_pos_of_neg hmid₀ h)) (hτ.le.trans hL)
  have hR₀ : 0 ≤ Real.log qR := Real.log_nonneg hqR₁
  refine ⟨(a+r)⁻¹+qR/(a-r), by positivity, fun U hU => ?_⟩
  have hU₀ : 0 ≤ U := zero_le_one.trans hU
  let n := ⌈a*mid*U⌉₊
  have hn₁ : a*mid*U ≤ (n:ℝ) := Nat.le_ceil _
  have hn₂ : (n:ℝ) < a*mid*U+1 := Nat.ceil_lt_add_one (by positivity)
  have hn₀ : U ≤ (n:ℝ) := by
    refine le_trans ?_ hn₁
    exact le_mul_of_one_le_left hU₀ (one_le_mul_of_one_le_of_one_le ha₁ hmid)
  refine ⟨n, hn₀, gammaMoment_tail_div_pow hr hra hb n ?_ ?_⟩
  · change r*U ≤ (n:ℝ)*Real.log qL
    calc
      r*U = a*U*τ := by dsimp [r]; ring
      _ ≤ a*U*(mid*Real.log qL) := mul_le_mul_of_nonneg_left hL (by positivity)
      _ = (a*mid*U)*Real.log qL := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hn₁ hL₀
  · change -r*((1+δ)*U) + (n:ℝ)*Real.log qR ≤ Real.log qR
    have hu := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ a*U)
    have hn := mul_le_mul_of_nonneg_right hn₂.le hR₀
    dsimp [r] at *
    nlinarith only [hu, hn]

/-- The complex Laplace moment with real decay parameter and Fourier frequency. -/
noncomputable def windowMoment (g : ℝ → ℝ) (σ γ : ℝ) (n : ℕ) : ℂ :=
  ∫ u in Ioi (0:ℝ), ((g u * gammaMoment σ n u : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (γ:ℂ) * (u:ℂ)))

private theorem windowMoment_zero_re (g : ℝ → ℝ) (σ : ℝ) (n : ℕ) :
    (windowMoment g σ 0 n).re = ∫ u in Ioi (0:ℝ), g u * gammaMoment σ n u := by
  unfold windowMoment
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero,
    mul_one, integral_complex_ofReal, Complex.ofReal_re]

private theorem windowMoment_norm_le (g : ℝ → ℝ) (σ γ : ℝ) (n : ℕ) :
    ‖windowMoment g σ γ n‖ ≤ ∫ u in Ioi (0:ℝ), |g u| * gammaMoment σ n u := by
  unfold windowMoment
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hc : (-(Complex.I * (γ:ℂ) * (u:ℂ))).re = 0 := by simp
  change ‖((g u * gammaMoment σ n u : ℝ):ℂ) * Complex.exp (-(Complex.I*(γ:ℂ)*(u:ℂ)))‖ =
    |g u| * gammaMoment σ n u
  rw [norm_mul, Complex.norm_exp, hc, Real.exp_zero, mul_one, Complex.norm_real, norm_mul,
    Real.norm_of_nonneg (gammaMoment_nonneg _ _ hu.le), Real.norm_eq_abs]

/-- A one-sided bound on a single scale interval yields an inequality between
the vertical and real moments. Outside the interval only a crude bound is used. -/
theorem windowMoment_le_of_one_sided {g : ℝ → ℝ} (hg : Measurable g)
    {B K θ C σ U V : ℝ} (_hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : B < σ) (hθ : θ < σ)
    (hglobal : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K * Real.exp (B*u))
    (hwin : ∀ u ∈ Icc U V, g u ≤ C * Real.exp (θ*u)) (n : ℕ) (γ : ℝ) :
    ‖windowMoment g σ γ n‖ + (windowMoment g σ 0 n).re ≤
      (2*C)/(σ-θ)^(n+1) +
        (2*K)*(∫ u in Ioi (0:ℝ) \ Icc U V, gammaMoment (σ-B) n u) := by
  let S := Ioi (0:ℝ) \ Icc U V
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  have hS : MeasurableSet S := measurableSet_Ioi.diff measurableSet_Icc
  have hsub : S ⊆ Ioi 0 := sdiff_subset
  have hwmeas : Measurable (gammaMoment σ n) := by unfold gammaMoment; fun_prop
  have hiB : Integrable (gammaMoment (σ-B) n) μ :=
    gammaMoment_integrable (sub_pos.mpr hB) n
  have hiθ : Integrable (gammaMoment (σ-θ) n) μ :=
    gammaMoment_integrable (sub_pos.mpr hθ) n
  have hM (u : ℝ) (hu : 0 ≤ u) :
      |g u| * gammaMoment σ n u ≤ K * gammaMoment (σ-B) n u := by
    calc
      _ ≤ (K*Real.exp (B*u))*gammaMoment σ n u :=
        mul_le_mul_of_nonneg_right (hglobal u hu) (gammaMoment_nonneg _ _ hu)
      _ = _ := by rw [mul_assoc, exp_mul_gammaMoment]
  have hiAbs : Integrable (fun u => |g u| * gammaMoment σ n u) μ := by
    refine (hiB.const_mul K).mono' (hg.abs.mul hwmeas).aestronglyMeasurable ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    refine Eventually.of_forall fun u hu => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (gammaMoment_nonneg _ _ hu.le))]
    exact hM u hu.le
  have hiG : Integrable (fun u => g u * gammaMoment σ n u) μ := by
    refine hiAbs.mono' (hg.mul hwmeas).aestronglyMeasurable ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    refine Eventually.of_forall fun u hu => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (gammaMoment_nonneg _ _ hu.le)]
  let H (u : ℝ) := (2*C)*gammaMoment (σ-θ) n u
  let T (u : ℝ) := (2*K)*gammaMoment (σ-B) n u
  have hiH : Integrable H μ := hiθ.const_mul _
  have hiT : Integrable T μ := hiB.const_mul _
  have hnonH (u : ℝ) (hu : 0 ≤ u) : 0 ≤ H u :=
    mul_nonneg (by positivity) (gammaMoment_nonneg _ _ hu)
  have hme : (∫ u, S.indicator T u ∂μ) = (2*K) * (∫ u in S, gammaMoment (σ-B) n u) := by
    rw [integral_indicator hS]
    dsimp only [μ, T]
    rw [Measure.restrict_restrict hS, inter_eq_left.mpr hsub, integral_const_mul]
  have hiM : Integrable (fun u => H u + S.indicator T u) μ := hiH.add (hiT.indicator hS)
  calc
    _ ≤ (∫ u, |g u| * gammaMoment σ n u ∂μ) + (∫ u, g u*gammaMoment σ n u ∂μ) := by
      rw [windowMoment_zero_re]
      exact add_le_add (windowMoment_norm_le _ _ _ _) le_rfl
    _ = ∫ u, |g u| * gammaMoment σ n u+g u*gammaMoment σ n u ∂μ := (integral_add hiAbs hiG).symm
    _ ≤ ∫ u, H u + S.indicator T u ∂μ := by
      apply integral_mono_ae (hiAbs.add hiG) hiM
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      refine Eventually.of_forall fun u hu => ?_
      change |g u| * gammaMoment σ n u + g u * gammaMoment σ n u ≤ H u + S.indicator T u
      by_cases hw : u ∈ Icc U V
      · have hs : u ∉ S := fun h => h.2 hw
        rw [indicator_of_notMem hs, add_zero, ← add_mul]
        have hg' : |g u|+g u ≤ (2*C)*Real.exp (θ*u) := by
          rcases le_or_gt 0 (g u) with h | h
          · rw [abs_of_nonneg h]
            have he := hwin u hw
            linarith
          · rw [abs_of_neg h]
            linarith [mul_nonneg hC (Real.exp_nonneg (θ*u))]
        calc
          _ ≤ ((2*C)*Real.exp (θ*u))*gammaMoment σ n u :=
            mul_le_mul_of_nonneg_right hg' (gammaMoment_nonneg _ _ hu.le)
          _ = _ := by rw [mul_assoc, exp_mul_gammaMoment]
      · have hs : u ∈ S := ⟨hu, hw⟩
        rw [indicator_of_mem hs]
        have hle := mul_le_mul_of_nonneg_right (le_abs_self (g u))
          (gammaMoment_nonneg σ n hu.le)
        have hM' := hM u hu.le
        dsimp [T]
        linarith [hnonH u hu.le]
    _ = _ := by
      rw [integral_add hiH (hiT.indicator hS), hme]
      dsimp only [H, μ]
      rw [integral_const_mul, gammaMoment_mass (sub_pos.mpr hθ)]
      ring

/-- Arbitrarily late one-sided bounds throughout relative scale intervals
force arbitrarily high moments to satisfy one uniform coefficient bound. -/
theorem windowMoment_bound_along_orders {g : ℝ → ℝ} (hg : Measurable g)
    {B K θ C δ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hθB : θ ≤ B) (hδ : 0 < δ)
    (hglobal : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K * Real.exp (B*u))
    (hwin : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∀ u ∈ Icc U ((1+δ)*U),
      g u ≤ C * Real.exp (θ*u)) :
    ∃ σ : ℝ, B < σ ∧ ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∀ γ : ℝ,
      ‖windowMoment g σ γ n‖ + (windowMoment g σ 0 n).re ≤ D/(σ-θ)^n := by
  obtain ⟨a, ha, hl⟩ := gammaMoment_localization δ (B-θ) hδ (sub_nonneg.mpr hθB)
  obtain ⟨L, hL, hL'⟩ := hl a le_rfl
  let σ := a+B
  have hB : B < σ := by dsimp [σ]; linarith
  have hθ : θ < σ := hθB.trans_lt hB
  let D := (2*C)/(σ-θ)+(2*K)*L
  refine ⟨σ, hB, D, by dsimp [D]; positivity, fun N => ?_⟩
  obtain ⟨U, hU, hu⟩ := hwin (max 1 (N:ℝ))
  obtain ⟨n, hn, htail⟩ := hL' U ((le_max_left _ _).trans hU)
  have hn' : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans hU).trans hn
  have haeq : a = σ-B := by dsimp [σ]; ring
  have hbeq : a+(B-θ) = σ-θ := by dsimp [σ]; ring
  rw [hbeq, haeq] at htail
  refine ⟨n, hn', fun γ => ?_⟩
  have hM := windowMoment_le_of_one_sided hg hK hC hB hθ hglobal hu n γ
  calc
    _ ≤ (2*C)/(σ-θ)^(n+1)+(2*K)*(L/(σ-θ)^n) :=
      hM.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left htail (by positivity)))
    _ = _ := by
      dsimp [D]
      rw [pow_succ]
      field_simp [(sub_pos.mpr hθ).ne']

end MasulloAlpoge

set_option autoImplicit false

open Complex Filter Set MeasureTheory Metric Topology

namespace MasulloAlpoge

private noncomputable def weightedIntegrand (g : ℝ → ℝ) (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (g u : ℂ) * (u:ℂ)^n * Complex.exp (-s*(u:ℂ))

private noncomputable def weightedLaplace (g : ℝ → ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Ioi (0:ℝ), weightedIntegrand g n s u

private theorem weightedIntegrand_measurable {g : ℝ → ℝ} (hg : Measurable g) (n : ℕ) (s : ℂ) :
    Measurable (weightedIntegrand g n s) := by
  unfold weightedIntegrand
  fun_prop

private theorem weightedIntegrand_bound {g : ℝ → ℝ} {K B b : ℝ}
    (hK : 0 ≤ K) (hg : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B+b ≤ s.re) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ‖weightedIntegrand g n s u‖ ≤ ((n.factorial:ℝ)*K)*gammaMoment b n u := by
  have hfact : 0 < (n.factorial:ℝ) := by exact_mod_cast n.factorial_pos
  have he : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  unfold weightedIntegrand
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_of_nonneg hu, Complex.norm_exp, he]
  have hG : |g u| * ((u^n)*Real.exp (-s.re*u)) ≤
      (K*Real.exp (B*u))*((u^n)*Real.exp (-s.re*u)) :=
    mul_le_mul_of_nonneg_right (hg u hu) (by positivity)
  have hshift : Real.exp (B*u) * Real.exp (-s.re*u) = Real.exp (-((s.re-B)*u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he' : Real.exp (-((s.re-B)*u)) ≤ Real.exp (-(b*u)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (by linarith) hu))
  calc
    _ = |g u| * ((u^n)*Real.exp (-s.re*u)) := by ring
    _ ≤ (K*Real.exp (B*u))*((u^n)*Real.exp (-s.re*u)) := hG
    _ = K*(u^n)*(Real.exp (B*u)*Real.exp (-s.re*u)) := by ring
    _ ≤ K*(u^n)*Real.exp (-(b*u)) := by rw [hshift]; exact mul_le_mul_of_nonneg_left he' (by positivity)
    _ = _ := by unfold gammaMoment; field_simp [hfact.ne']

private theorem integrable_weightedIntegrand {g : ℝ → ℝ} (hg : Measurable g) {K B b : ℝ}
    (hK : 0 ≤ K) (hb : 0 < b) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B+b ≤ s.re) (n : ℕ) :
    IntegrableOn (weightedIntegrand g n s) (Ioi 0) := by
  refine ((gammaMoment_integrable hb n).const_mul ((n.factorial:ℝ)*K)).mono'
    (weightedIntegrand_measurable hg n s).aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun u hu => weightedIntegrand_bound hK hgK hs n hu.le)

private theorem hasDerivAt_weightedLaplace {g : ℝ → ℝ} (hg : Measurable g) {K B : ℝ}
    (hK : 0 ≤ K) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B < s.re) (n : ℕ) :
    HasDerivAt (weightedLaplace g n) (-weightedLaplace g (n+1) s) s := by
  let b := (s.re-B)/2
  have hb : 0 < b := by dsimp [b]; linarith
  have hz (z : ℂ) (hz : z ∈ ball s b) : B+b ≤ z.re := by
    have hd : ‖z-s‖ < b := by simpa only [mem_ball, dist_eq_norm] using hz
    have hr := (abs_lt.mp ((Complex.abs_re_le_norm (z-s)).trans_lt hd)).1
    simp only [Complex.sub_re] at hr
    dsimp [b] at hr ⊢
    linarith
  have hbnd : ∀ᵐ u ∂(volume : Measure ℝ).restrict (Ioi 0), ∀ z ∈ ball s b,
      ‖-weightedIntegrand g (n+1) z u‖ ≤ (((n+1).factorial:ℝ)*K)*gammaMoment b (n+1) u :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu z hzs => by
      rw [norm_neg]
      exact weightedIntegrand_bound hK hgK (hz z hzs) (n+1) hu.le)
  have hder (u : ℝ) (z : ℂ) :
      HasDerivAt (fun w => weightedIntegrand g n w u) (-weightedIntegrand g (n+1) z u) z := by
    have he : HasDerivAt (fun w : ℂ => -w*(u:ℂ)) (-(u:ℂ)) z := by
      simpa using (hasDerivAt_id z).neg.mul_const (u:ℂ)
    refine (he.cexp.const_mul ((g u : ℂ)*(u:ℂ)^n)).congr_deriv ?_
    unfold weightedIntegrand
    rw [pow_succ]
    ring
  have hi := (gammaMoment_integrable hb (n+1)).const_mul (((n+1).factorial:ℝ)*K)
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := weightedIntegrand g n) (F' := fun z u => -weightedIntegrand g (n+1) z u)
    (ball_mem_nhds s hb)
    (Eventually.of_forall fun z => (weightedIntegrand_measurable hg n z).aestronglyMeasurable)
    (integrable_weightedIntegrand hg hK hb hgK (hz s (mem_ball_self hb)) n)
    ((weightedIntegrand_measurable hg (n+1) s).neg.aestronglyMeasurable)
    hbnd hi (Eventually.of_forall fun u z _ => hder u z)).2
  unfold weightedLaplace
  rw [← integral_neg]
  exact hh

private theorem iteratedDeriv_weightedLaplace {g : ℝ → ℝ} (hg : Measurable g) {K B : ℝ}
    (hK : 0 ≤ K) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    (n : ℕ) :
    ∀ s : ℂ, B < s.re →
      iteratedDeriv n (weightedLaplace g 0) s = (-1:ℂ)^n*weightedLaplace g n s := by
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
    intro s hs
    have hopen : IsOpen {z : ℂ | B < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hnear : ∀ᶠ z : ℂ in 𝓝 s, B < z.re := hopen.mem_nhds hs
    have he : iteratedDeriv n (weightedLaplace g 0) =ᶠ[𝓝 s]
        (fun z => (-1:ℂ)^n * weightedLaplace g n z) :=
      hnear.mono (fun z hz => ih z hz)
    rw [iteratedDeriv_succ, he.deriv_eq,
      ((hasDerivAt_weightedLaplace hg hK hgK hs n).const_mul ((-1:ℂ)^n)).deriv]
    rw [pow_succ]
    ring

/-- The signed Taylor coefficient at a point in the half-plane. -/
noncomputable def windowCoefficient (Φ : ℂ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  (-1:ℂ)^n * iteratedDeriv n Φ s / (n.factorial : ℂ)

/-- The integral window moments are precisely the signed Taylor coefficients
of the analytic continuation on the initial half-plane. -/
theorem windowCoefficient_eq_moment {g : ℝ → ℝ} {Φ : ℂ → ℂ} (hg : Measurable g)
    {K B : ℝ} (hK : 0 ≤ K) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    (hΦ : ∀ s : ℂ, B < s.re → Φ s =
      ∫ u in Ioi (0:ℝ), (g u : ℂ)*Complex.exp (-s*(u:ℂ)))
    {σ : ℝ} (hσ : B < σ) (γ : ℝ) (n : ℕ) :
    windowCoefficient Φ ((σ:ℂ)+(γ:ℂ)*I) n = windowMoment g σ γ n := by
  let s := (σ:ℂ)+(γ:ℂ)*I
  have hs : B < s.re := by simpa [s] using hσ
  have hlo : IsOpen {z : ℂ | B < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hnear : ∀ᶠ z : ℂ in 𝓝 s, B < z.re := hlo.mem_nhds hs
  have he : Φ =ᶠ[𝓝 s] weightedLaplace g 0 := by
    refine hnear.mono ?_
    intro z hz
    simpa [weightedLaplace, weightedIntegrand] using hΦ z hz
  change windowCoefficient Φ s n = _
  unfold windowCoefficient
  rw [he.iteratedDeriv_eq, iteratedDeriv_weightedLaplace hg hK hgK n s hs, ← mul_assoc, ← mul_pow]
  simp only [neg_mul_neg, one_mul, one_pow]
  unfold weightedLaplace windowMoment
  rw [← integral_div]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  have hphase : Complex.exp (-s*(u:ℂ)) = ((Real.exp (-σ*u):ℝ):ℂ) *
      Complex.exp (-(I*(γ:ℂ)*(u:ℂ))) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp [s]
    push_cast
    ring
  change weightedIntegrand g n s u/(n.factorial:ℂ) = _
  unfold weightedIntegrand gammaMoment
  rw [hphase]
  push_cast
  ring

theorem laplace_integrable_of_exponential_bound {g : ℝ → ℝ} (hg : Measurable g)
    {K B : ℝ} (hK : 0 ≤ K) (hgK : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    {s : ℂ} (hs : B < s.re) :
    IntegrableOn (fun u : ℝ => (g u:ℂ)*Complex.exp (-s*(u:ℂ))) (Ioi 0) := by
  have hb : 0 < s.re-B := sub_pos.mpr hs
  have hσ : B+(s.re-B) ≤ s.re := by linarith
  have h := integrable_weightedIntegrand hg hK hb hgK hσ 0
  have he : weightedIntegrand g 0 s = (fun u : ℝ => (g u:ℂ)*Complex.exp (-s*(u:ℂ))) := by
    funext u
    simp [weightedIntegrand]
  rwa [he] at h

theorem linear_exponential_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => (u:ℂ)*Complex.exp (-s*(u:ℂ))) (Ioi 0) := by
  have h := integrable_weightedIntegrand
    (g := fun _ => (1:ℝ)) measurable_const (K := 1) (B := 0) zero_le_one hs
      (fun u _ => by simp) (s := s) (by simp : (0:ℝ)+s.re ≤ s.re) 1
  have he : weightedIntegrand (fun _ => 1) 1 s =
      (fun u : ℝ => (u:ℂ)*Complex.exp (-s*(u:ℂ))) := by
    funext u
    simp [weightedIntegrand]
  rwa [he] at h

/-- The first moment of a complex exponential with positive decay. -/
theorem linear_exponential_integral {s : ℂ} (hs : 0 < s.re) :
    (∫ u in Ioi (0:ℝ), (u:ℂ)*Complex.exp (-s*(u:ℂ))) = 1/s^2 := by
  have he (z : ℂ) (hz : 0 < z.re) :
      weightedLaplace (fun _ => 1) 0 z = z⁻¹ := by
    have h := integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
    simpa [weightedLaplace, weightedIntegrand, div_eq_mul_inv] using h
  have hnear : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  have hlocal : weightedLaplace (fun _ => 1) 0 =ᶠ[𝓝 s] (fun z : ℂ => z⁻¹) :=
    hnear.mono he
  have hd : HasDerivAt (weightedLaplace (fun _ => 1) 0) (-weightedLaplace (fun _ => 1) 1 s) s :=
    hasDerivAt_weightedLaplace measurable_const (K := 1) (B := 0) zero_le_one
      (fun u _ => by simp) hs 0
  have hz : s ≠ 0 := ne_zero_of_re_pos hs
  have hInv := hasDerivAt_inv (x := s) hz
  have ht := hd.deriv.symm.trans (hlocal.deriv_eq.trans hInv.deriv)
  simpa [weightedLaplace, weightedIntegrand, div_eq_mul_inv] using neg_injective ht

end MasulloAlpoge

set_option autoImplicit false

open Complex Filter MeasureTheory Metric Set Topology

namespace MasulloAlpoge

/-- Move along the vertical line with real part `σ`. -/
def windowCenter (σ γ : ℝ) : ℂ := (σ:ℂ)+(γ:ℂ)*I

@[simp] theorem windowCenter_re (σ γ : ℝ) : (windowCenter σ γ).re = σ := by simp [windowCenter]
@[simp] theorem windowCenter_im (σ γ : ℝ) : (windowCenter σ γ).im = γ := by simp [windowCenter]

private theorem windowCenter_dist (σ γ γ₀ : ℝ) :
    dist (windowCenter σ γ) (windowCenter σ γ₀) = |γ-γ₀| := by
  rw [dist_eq_norm]
  have he : windowCenter σ γ-windowCenter σ γ₀ = (((γ-γ₀:ℝ):ℂ))*I := by
    unfold windowCenter
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

private theorem dist_windowCenter_sq (z : ℂ) (σ γ : ℝ) :
    (dist z (windowCenter σ γ))^2 = (z.re-σ)^2+(z.im-γ)^2 := by
  rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, windowCenter_re, windowCenter_im]
  ring

private theorem dist_projection_lt (z : ℂ) (σ : ℝ) (hz : z.im ≠ 0) :
    dist z (windowCenter σ z.im) < dist z (σ:ℂ) := by
  have hn (γ : ℝ) : 0 ≤ dist z (windowCenter σ γ) := dist_nonneg
  have hz0 : windowCenter σ 0 = (σ:ℂ) := by simp [windowCenter]
  have hS := dist_windowCenter_sq z σ z.im
  have hZ := dist_windowCenter_sq z σ 0
  rw [hz0] at hZ
  have hp : 0 < z.im^2 := sq_pos_of_ne_zero hz
  by_contra! he
  have hs := pow_le_pow_left₀ (show 0 ≤ dist z (σ:ℂ) from dist_nonneg) he 2
  nlinarith

private theorem continuous_distance_to (c : ℂ) : Continuous (fun z : ℂ => dist z c) :=
  continuous_id.dist continuous_const

private theorem compact_poles_in_disk {Z : Set ℂ} (hZ : IsClosed Z) (hDisc : IsDiscrete Z)
    (s : ℂ) (r : ℝ) : (closedBall s r ∩ Z).Finite := by
  exact ((isCompact_closedBall s r).inter_right hZ).finite (hDisc.mono inter_subset_right)

private theorem reference_disk {Z : Set ℂ} (hZ : IsClosed Z)
    (hZim : ∀ z ∈ Z, z.im ≠ 0) (σ θ : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ Z) (hρlo : θ < ρ.re) (hρhi : ρ.re < σ) :
    ∃ R : ℝ, 0 < R ∧ R ≤ σ-θ ∧ Disjoint (ball (σ:ℂ) R) Z ∧
      ∃ γ : ℝ, ∃ z ∈ Z, dist z (windowCenter σ γ) < R := by
  let E := σ-θ
  have hE : 0 < E := by dsimp [E]; linarith
  by_cases h : (ball (σ:ℂ) E ∩ Z).Nonempty
  · obtain ⟨w, hw⟩ := h
    let C := closedBall (σ:ℂ) (dist w (σ:ℂ)) ∩ Z
    have hwC : w ∈ C := ⟨mem_closedBall.mpr le_rfl, hw.2⟩
    have hC : IsCompact C := (isCompact_closedBall _ _).inter_right hZ
    obtain ⟨z,hz,hm⟩ := hC.exists_isMinOn ⟨w,hwC⟩ (continuous_distance_to (σ:ℂ)).continuousOn
    have hmin := isMinOn_iff.mp hm
    let R := dist z (σ:ℂ)
    have hRpos : 0 < R := dist_pos.mpr (by
      intro he
      exact hZim z hz.2 (by rw [he, Complex.ofReal_im]))
    have hRle : R ≤ dist w (σ:ℂ) := hmin w hwC
    have hwlt : dist w (σ:ℂ) < E := hw.1
    refine ⟨R, hRpos, (hRle.trans_lt hwlt).le, ?_, z.im, z, hz.2,
      dist_projection_lt z σ (hZim z hz.2)⟩
    apply Set.disjoint_left.mpr
    intro y hy hyZ
    have hy' : dist y (σ:ℂ) < R := hy
    exact not_lt_of_ge (hmin y ⟨mem_closedBall.mpr (hy'.le.trans hRle),hyZ⟩) hy'
  · let R := ((σ-ρ.re)+E)/2
    have hR₀ : 0 < R := by dsimp [R]; linarith
    have hR₁ : R < E := by dsimp [R, E]; linarith
    have hρR : σ-ρ.re < R := by dsimp [R, E]; linarith
    refine ⟨R,hR₀,hR₁.le,?_,ρ.im,ρ,hρ,?_⟩
    · apply Set.disjoint_left.mpr
      intro y hy hyZ
      exact h ⟨y,(mem_ball.mpr ((mem_ball.mp hy).trans hR₁)),hyZ⟩
    · have hd : dist ρ (windowCenter σ ρ.im) = σ-ρ.re := by
        rw [dist_eq_norm]
        have he : ρ-windowCenter σ ρ.im = ((ρ.re-σ:ℝ):ℂ) := by apply Complex.ext <;> simp
        rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hρhi), neg_sub]
      exact hd ▸ hρR

private noncomputable def collisionHeight (σ : ℝ) (a b : ℂ) : ℝ :=
  ((a.re-σ)^2+a.im^2-((b.re-σ)^2+b.im^2))/(2*(a.im-b.im))

private theorem collisionHeight_of_equal_distance {a b : ℂ} (hab : a ≠ b)
    {σ γ : ℝ} (ha : a.re < σ) (hb : b.re < σ)
    (he : dist a (windowCenter σ γ) = dist b (windowCenter σ γ)) :
    γ = collisionHeight σ a b := by
  have h := congrArg (fun x : ℝ => x^2) he
  rw [dist_windowCenter_sq, dist_windowCenter_sq] at h
  have him : a.im ≠ b.im := by
    intro heq
    have hre : (a.re-σ)^2 = (b.re-σ)^2 := by rw [heq] at h; linarith
    have hmul : ((a.re-σ)-(b.re-σ))*((a.re-σ)+(b.re-σ)) = 0 := by nlinarith only [hre]
    have hs : (a.re-σ)+(b.re-σ) ≠ 0 := by linarith
    have hr : a.re = b.re := by
      rcases mul_eq_zero.mp hmul with h' | h'
      · linarith
      · exact False.elim (hs h')
    exact hab (Complex.ext hr heq)
  unfold collisionHeight
  apply (eq_div_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr him))).mpr
  nlinarith only [h]

private theorem pick_vertical_center {Z : Set ℂ} (hZ : IsClosed Z) (hDisc : IsDiscrete Z)
    (σ : ℝ) (hRe : ∀ z ∈ Z, z.re < σ) {R : ℝ}
    (γ₀ : ℝ) {p : ℂ} (hpR : dist p (windowCenter σ γ₀) < R) :
    ∃ γ : ℝ, dist p (windowCenter σ γ) < R ∧
      ∀ a b : ℂ, a ∈ Z → b ∈ Z → dist a (windowCenter σ γ) < R →
        dist b (windowCenter σ γ) < R →
        dist a (windowCenter σ γ) = dist b (windowCenter σ γ) → a = b := by
  let C := closedBall (windowCenter σ γ₀) (R+1) ∩ Z
  have hC : C.Finite := compact_poles_in_disk hZ hDisc _ _
  let Bad := (fun ab : ℂ × ℂ => collisionHeight σ ab.1 ab.2) '' (C.prod C)
  have hBad : Bad.Finite := (hC.prod hC).image _
  let ε := min 1 ((R-dist p (windowCenter σ γ₀))/2)
  have hε : 0 < ε := lt_min zero_lt_one (by linarith)
  have hε₁ : ε ≤ 1 := min_le_left _ _
  have hε₂ : ε ≤ (R-dist p (windowCenter σ γ₀))/2 := min_le_right _ _
  obtain ⟨γ,hγ,hnot⟩ := ((Set.Ioo_infinite (a:=γ₀-ε) (b:=γ₀+ε) (by linarith )).sdiff hBad).nonempty
  have hdist : dist (windowCenter σ γ) (windowCenter σ γ₀) < ε := by
    rw [windowCenter_dist, abs_lt]
    exact ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
  have hC' (a : ℂ) (ha : a ∈ Z) (h : dist a (windowCenter σ γ) < R) : a ∈ C := by
    refine ⟨mem_closedBall.mpr ?_,ha⟩
    have hT := dist_triangle a (windowCenter σ γ) (windowCenter σ γ₀)
    linarith
  have hp' : dist p (windowCenter σ γ) < R := by
    have hT := dist_triangle p (windowCenter σ γ₀) (windowCenter σ γ)
    rw [dist_comm (windowCenter σ γ₀)] at hT
    linarith
  refine ⟨γ,hp',fun a b ha hb haR hbR he => ?_⟩
  by_contra hn
  have h := collisionHeight_of_equal_distance hn (hRe a ha) (hRe b hb) he
  exact hnot ⟨(a,b), ⟨hC' a ha haR,hC' b hb hbR⟩, h.symm⟩

/-- Isolate a pole in a disk about a vertical translate. A larger disk with
the same radius bound about the real center contains no pole. -/
theorem isolate_window_pole {Z : Set ℂ} (hZ : IsClosed Z) (hDisc : IsDiscrete Z)
    (hIm : ∀ z ∈ Z, z.im ≠ 0) {σ θ : ℝ} (hRe : ∀ z ∈ Z, z.re < σ)
    {ρ : ℂ} (hρ : ρ ∈ Z) (hρlo : θ < ρ.re) :
    ∃ R γ r : ℝ, ∃ z ∈ Z, 0 < dist z (windowCenter σ γ) ∧
      dist z (windowCenter σ γ) < r ∧ r ≤ R ∧ R ≤ σ-θ ∧
      Disjoint (ball (σ:ℂ) R) Z ∧
      ∀ w ∈ Z, w ∈ ball (windowCenter σ γ) r → w = z := by
  obtain ⟨R,hR,hRE,hfree,γ₀,p,hp,hpR⟩ :=
    reference_disk hZ hIm σ θ hρ hρlo (hRe ρ hρ)
  obtain ⟨γ,hp',hg⟩ := pick_vertical_center hZ hDisc σ hRe γ₀ hpR
  let c := windowCenter σ γ
  let S := closedBall c (dist p c) ∩ Z
  have hS : IsCompact S := (isCompact_closedBall _ _).inter_right hZ
  obtain ⟨z,hz,hmin⟩ := hS.exists_isMinOn ⟨p,mem_closedBall.mpr le_rfl,hp⟩ (continuous_distance_to c).continuousOn
  let d := dist z c
  have hd₀ : 0 < d := dist_pos.mpr (by
    intro he
    have hzre := hRe z hz.2
    rw [he, show c.re = σ from windowCenter_re σ γ] at hzre
    exact lt_irrefl _ hzre)
  have hdR : d < R := ((mem_closedBall.mp hz.1).trans_lt hp')
  let T := (closedBall c R ∩ Z) \ {z}
  have hTf : T.Finite := (compact_poles_in_disk hZ hDisc _ _).subset sdiff_subset
  have hT := hTf.isCompact
  have ht (w : ℂ) (hw : w ∈ T) : d < dist w c := by
    by_contra! he
    have hw' : w ∈ S := ⟨mem_closedBall.mpr (he.trans (mem_closedBall.mp hz.1)),hw.1.2⟩
    have hl : d ≤ dist w c := (isMinOn_iff.mp hmin) w hw'
    have heq := le_antisymm hl he
    have hweq := hg z w hz.2 hw.1.2 hdR (he.trans_lt hdR) heq
    exact hw.2 (mem_singleton_iff.mpr hweq.symm)
  have hex : ∃ r : ℝ, d < r ∧ r ≤ R ∧ ∀ w ∈ T, r ≤ dist w c := by
    by_cases hn : T.Nonempty
    · obtain ⟨w,hw,hm⟩ := hT.exists_isMinOn hn (continuous_distance_to c).continuousOn
      refine ⟨min R (dist w c), lt_min hdR (ht w hw), min_le_left _ _, fun v hv => ?_⟩
      exact (min_le_right _ _).trans ((isMinOn_iff.mp hm) v hv)
    · exact ⟨R,hdR,le_rfl,fun w hw => False.elim (hn ⟨w,hw⟩)⟩
  obtain ⟨r,hr,hrR,hrw⟩ := hex
  refine ⟨R,γ,r,z,hz.2,hd₀,hr,hrR,hRE,hfree,fun w hw hwball => ?_⟩
  by_contra hn
  have hwr : dist w c < r := hwball
  exact not_lt_of_ge (hrw w ⟨⟨mem_closedBall.mpr (hwr.le.trans hrR),hw⟩,
    fun he => hn (mem_singleton_iff.mp he)⟩) hwr

end MasulloAlpoge

set_option autoImplicit false

open Complex Filter Set Metric MeasureTheory Topology

namespace MasulloAlpoge

private theorem windowCoefficient_bound {f : ℂ → ℂ} {z : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hf : DifferentiableOn ℂ f (ball z R)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖windowCoefficient f z n‖ ≤ M/r^n := by
  have h₁ : sphere z r ⊆ ball z R := fun w hw => by
    rw [mem_ball, mem_sphere.mp hw]
    exact hrR
  have h₂ : closedBall z r ⊆ ball z R := fun w hw => by
    exact mem_ball.mpr ((mem_closedBall.mp hw).trans_lt hrR)
  have hF : DiffContOnCl ℂ f (ball z r) := by
    refine ⟨hf.mono (ball_subset_ball hrR.le), ?_⟩
    rw [closure_ball _ hr.ne']
    exact hf.continuousOn.mono h₂
  obtain ⟨Q,hQ⟩ := (isCompact_sphere z r).exists_bound_of_continuousOn (hf.continuousOn.mono h₁)
  let M := max 0 Q
  refine ⟨M, le_max_left _ _, fun n => ?_⟩
  have hbound := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (C := M) n hr hF
    (fun w hw => (hQ w hw).trans (le_max_right _ _))
  have hfac : 0 < (n.factorial:ℝ) := by exact_mod_cast n.factorial_pos
  unfold windowCoefficient
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
  rw [div_le_iff₀ hfac]
  simpa only [mul_comm _ (n.factorial:ℝ), mul_div_assoc] using hbound

private theorem windowCoefficient_simplePole (c ρ z : ℂ) {n : ℕ} :
    windowCoefficient (fun w => c/(w-ρ)) z n = c/(z-ρ)^(n+1) := by
  have h₁ := iteratedDerivWithin_one_div (𝕜 := ℂ) n
    (s := (univ : Set ℂ)) isOpen_univ (mem_univ (z-ρ))
  simp only [iteratedDerivWithin_univ] at h₁
  unfold windowCoefficient
  have hs :
      iteratedDeriv n (fun w : ℂ => 1/(w-ρ)) z =
        (-1:ℂ)^n*(n.factorial:ℂ)*(z-ρ)^(-1-(n:ℤ)) := by
    have hg := congrFun (iteratedDeriv_comp_sub_const (n := n) (f := fun w : ℂ => 1/w) (s := ρ)) z
    exact hg.trans h₁
  rw [show (fun w : ℂ => c/(w-ρ)) = (fun w : ℂ => c*(1/(w-ρ))) by
      funext w; rw [mul_one_div],
    iteratedDeriv_const_mul_field, hs]
  have hneq : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have he : (-1:ℤ)-(n:ℤ) = -((n+1:ℕ):ℤ) := by push_cast; omega
  rw [he, zpow_neg, zpow_natCast]
  calc
    _ = ((-1:ℂ)^n*(-1:ℂ)^n)*c*((n.factorial:ℂ)/(n.factorial:ℂ))*((z-ρ)^(n+1))⁻¹ := by ring
    _ = _ := by rw [← mul_pow, neg_mul_neg, one_mul, one_pow, div_self hneq, one_mul, mul_one, div_eq_mul_inv]

private theorem subtract_pole_on_disk {Φ : ℂ → ℂ} {z ρ c : ℂ} {R : ℝ}
    (hρ : ρ ∈ ball z R) (hf : DifferentiableOn ℂ Φ (ball z R \ {ρ}))
    (hp : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      ∀ᶠ w in 𝓝[≠] ρ, Φ w = c/(w-ρ)+H w) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball z R) ∧
      ∀ w ∈ ball z R \ {ρ}, Φ w = c/(w-ρ)+f w := by
  obtain ⟨H,hHan,hH⟩ := hp
  let f : ℂ → ℂ := Function.update (fun w => Φ w-c/(w-ρ)) ρ (H ρ)
  have hEq : f =ᶠ[𝓝 ρ] H := by
    rw [eventually_nhdsWithin_iff] at hH
    filter_upwards [hH] with w hw
    rcases eq_or_ne w ρ with rfl | hne
    · simp [f]
    · have h := hw (mem_compl_singleton_iff.mpr hne)
      rw [show f w = Φ w-c/(w-ρ) from Function.update_of_ne hne _ _ ,h]
      ring
  refine ⟨f, ?_, ?_⟩
  · intro w hw
    rcases eq_or_ne w ρ with rfl | hne
    · exact (hEq.differentiableAt_iff.mpr hHan.differentiableAt).differentiableWithinAt
    · have hmem : w ∈ ball z R \ {ρ} := ⟨hw,hne⟩
      have hopen : IsOpen (ball z R \ {ρ}) := isOpen_ball.sdiff isClosed_singleton
      have hnear : ∀ᶠ v : ℂ in 𝓝 w, v ∈ ball z R \ {ρ} := hopen.mem_nhds hmem
      have hwΦ := (hf w hmem).differentiableAt (hopen.mem_nhds hmem)
      have hwf : f =ᶠ[𝓝 w] (fun v => Φ v-c/(v-ρ)) :=
        hnear.mono (fun v hv => Function.update_of_ne hv.2 _ _)
      have hd : DifferentiableAt ℂ (fun v : ℂ => c/(v-ρ)) w :=
        (differentiableAt_const c).div (differentiableAt_id.sub_const _) (sub_ne_zero.mpr hne)
      exact (hwf.differentiableAt_iff.mpr (hwΦ.sub hd)).differentiableWithinAt
  · intro w hw
    rw [show f w = Φ w-c/(w-ρ) from Function.update_of_ne hw.2 _ _]
    ring

/-- A simple pole isolated inside a larger analytic disk gives a leading
Taylor term, with all other terms bounded at the larger radius. -/
theorem windowCoefficient_pole_asymptotic {Φ : ℂ → ℂ} {z ρ c : ℂ} {r R : ℝ}
    (hρ : ρ ∈ ball z R) (hzρ : z ≠ ρ) (hr : 0 < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ Φ (ball z R \ {ρ}))
    (hp : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      ∀ᶠ w in 𝓝[≠] ρ, Φ w = c/(w-ρ)+H w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      ‖windowCoefficient Φ z n - c/(z-ρ)^(n+1)‖ ≤ M/r^n := by
  obtain ⟨f,hf₁,hf₂⟩ := subtract_pole_on_disk hρ hf hp
  obtain ⟨M,hM,hbound⟩ := windowCoefficient_bound hr hrR hf₁
  refine ⟨M,hM,fun n => ?_⟩
  have hR : 0 < R := hr.trans hrR
  have hn : ∀ᶠ w : ℂ in 𝓝 z, w ∈ ball z R \ {ρ} :=
    (isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨mem_ball_self hR, hzρ⟩
  have he : Φ =ᶠ[𝓝 z] (fun w : ℂ => c/(w-ρ)) + f := hn.mono (fun w hw => hf₂ w hw)
  have hcp : ContDiffAt ℂ n (fun w : ℂ => c/(w-ρ)) z :=
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hzρ)
  have hcf : ContDiffAt ℂ n f z := (hf₁.contDiffOn isOpen_ball).contDiffAt
    (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hsum :
      windowCoefficient Φ z n =
        windowCoefficient (fun w : ℂ => c/(w-ρ)) z n + windowCoefficient f z n := by
    unfold windowCoefficient
    rw [he.iteratedDeriv_eq, iteratedDeriv_add hcp hcf]
    ring
  rw [hsum, windowCoefficient_simplePole, add_sub_cancel_left]
  exact hbound n

private theorem positive_constant_not_bounded_by_two_smaller_rates
    {c d e E M D : ℝ} (hc : 0 < c) (hd : 0 < d) (he : d < e) (heE : e ≤ E)
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c/d^n ≤ M/e^n + D/E^n) :
    False := by
  have he₀ : 0 < e := hd.trans he
  have hE : 0 < E := he₀.trans_le heE
  have hl : Tendsto (fun n : ℕ => M*(d/e)^n + D*(d/E)^n) atTop (𝓝 0) := by
    have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le he₀.le)
      ((div_lt_one he₀).mpr he)
    have h₂ := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le hE.le)
      ((div_lt_one hE).mpr (he.trans_le heE))
    simpa only [mul_zero, add_zero] using (h₁.const_mul M).add (h₂.const_mul D)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hl).2 c hc)
  obtain ⟨n,hn,hb⟩ := h N
  have hsmall := hN n hn
  have hb' := mul_le_mul_of_nonneg_right hb (pow_nonneg hd.le n)
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hd.ne'), add_mul] at hb'
  have h₁ : M/e^n*d^n = M*(d/e)^n := by rw [div_pow]; ring
  have h₂ : D/E^n*d^n = D*(d/E)^n := by rw [div_pow]; ring
  rw [h₁,h₂] at hb'
  exact (not_lt_of_ge hb') hsmall

/-- A one-sided bound on arbitrarily late relative windows rules out poles
right of the window exponent, when the poles are disjoint from the real line. -/
theorem no_nonreal_poles_of_upper_windows {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hZ : IsClosed Z) (hZd : IsDiscrete Z) (hIm : ∀ z ∈ Z, z.im ≠ 0)
    (hg : Measurable g) {B K θ C δ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hθB : θ ≤ B) (hδ : 0 < δ)
    (hglobal : ∀ u : ℝ, 0 ≤ u → |g u| ≤ K*Real.exp (B*u))
    (hwin : ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∀ u ∈ Icc U ((1+δ)*U),
      g u ≤ C * Real.exp (θ*u))
    (hΦ : ∀ s : ℂ, B < s.re → Φ s =
      ∫ u in Ioi (0:ℝ), (g u:ℂ)*Complex.exp (-s*(u:ℂ)))
    (hRe : ∀ z ∈ Z, z.re ≤ B)
    (hdiff : ∀ s : ℂ, θ < s.re → s ∉ Z → DifferentiableAt ℂ Φ s)
    (hPole : ∀ ρ ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ ∃ H : ℂ → ℂ, AnalyticAt ℂ H ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, Φ s = c/(s-ρ)+H s) : ∀ ρ ∈ Z, ρ.re ≤ θ := by
  intro ρ hρ
  by_contra! hρθ
  obtain ⟨σ,hσ,D,hD,hM⟩ := windowMoment_bound_along_orders hg hK hC hθB hδ hglobal hwin
  obtain ⟨R,γ,r,w,hw,hpos,hwr,hrR,hRE,hfree,hsole⟩ :=
    isolate_window_pole hZ hZd hIm (fun s hs => (hRe s hs).trans_lt hσ) hρ hρθ
  let z := windowCenter σ γ
  let d := dist w z
  let e := (d+r)/2
  have he₁ : d < e := by dsimp [e]; linarith
  have her : e < r := by dsimp [e]; linarith
  have he₀ : 0 < e := hpos.trans he₁
  have heR : e < R := her.trans_le hrR
  have hzρ : z ≠ w := by
    intro he
    rw [← he, dist_self] at hpos
    exact (lt_irrefl _) hpos
  have hhalf (c : ℂ) (hc : c.re = σ) (s : ℂ) (h : s ∈ ball c (σ-θ)) : θ < s.re := by
    have hnorm : ‖s-c‖ < σ-θ := by simpa only [mem_ball, dist_eq_norm] using h
    have h' := (abs_lt.mp ((Complex.abs_re_le_norm (s-c)).trans_lt hnorm)).1
    rw [Complex.sub_re,hc] at h'
    linarith
  have hreal : DifferentiableOn ℂ Φ (ball (σ:ℂ) R) := by
    intro s hs
    exact (hdiff s (hhalf _ (Complex.ofReal_re _) s (ball_subset_ball hRE hs))
      (fun hz' => (Set.disjoint_left.mp hfree) hs hz')).differentiableWithinAt
  have hvertical : DifferentiableOn ℂ Φ (ball z r \ {w}) := by
    intro s hs
    exact (hdiff s (hhalf z (windowCenter_re _ _) s (ball_subset_ball (hrR.trans hRE) hs.1))
      (fun he => hs.2 (hsole s he hs.1))).differentiableWithinAt
  obtain ⟨c,hcnz,hP⟩ := hPole w hw
  obtain ⟨M,hM₀,hv⟩ := windowCoefficient_pole_asymptotic (mem_ball.mpr hwr) hzρ he₀ her hvertical hP
  obtain ⟨M',hM'₀,hr'⟩ := windowCoefficient_bound he₀ heR hreal
  have hc : 0 < ‖c‖/d := div_pos (norm_pos_iff.mpr hcnz) hpos
  refine positive_constant_not_bounded_by_two_smaller_rates hc hpos he₁
    (heR.le.trans hRE) (M := M+M') (D := D) (fun N => ?_)
  obtain ⟨n,hn,hN⟩ := hM N
  refine ⟨n,hn,?_⟩
  have hz := hN γ
  rw [← windowCoefficient_eq_moment hg hK hglobal hΦ hσ γ n,
    ← windowCoefficient_eq_moment hg hK hglobal hΦ hσ 0 n] at hz
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hz
  have hV : ‖windowCoefficient Φ z n‖+(windowCoefficient Φ (σ:ℂ) n).re ≤ D/(σ-θ)^n := hz
  have hU := hv n
  have hRnorm := hr' n
  have hre : -‖windowCoefficient Φ (σ:ℂ) n‖ ≤ (windowCoefficient Φ (σ:ℂ) n).re :=
    (abs_le.mp (Complex.abs_re_le_norm _)).1
  have hcoef := norm_sub_norm_le (c/(z-w)^(n+1)) (windowCoefficient Φ z n)
  rw [norm_sub_rev] at hcoef
  have hdist : ‖z-w‖ = d := by rw [← dist_eq_norm, dist_comm]
  rw [norm_div, norm_pow, hdist, pow_succ', ← div_div] at hcoef
  rw [add_div]
  linarith

end MasulloAlpoge

set_option autoImplicit false

open Complex Filter Set Topology

namespace MasulloAlpoge

private theorem analyticAt_dslope_of_analyticAt {f : ℂ → ℂ} {z : ℂ}
    (h : AnalyticAt ℂ f z) : AnalyticAt ℂ (dslope f z) z := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

private noncomputable def zetaWindowNumerator (s : ℂ) : ℂ :=
  (1 + (Real.eulerMascheroniConstant:ℂ))*s - 1 - deriv riemannZeta₁ s / riemannZeta₁ s

/-- The regularized transform of the Riemann-zeta ramp error, with
the singularity at one removed. -/
noncomputable def zetaWindowTransform (s : ℂ) : ℂ :=
  dslope zetaWindowNumerator 1 s / s

private theorem zetaWindowNumerator_one : zetaWindowNumerator 1 = 0 := by
  simp [zetaWindowNumerator]

private theorem zetaWindowNumerator_analytic {s : ℂ} (h : riemannZeta₁ s ≠ 0) :
    AnalyticAt ℂ zetaWindowNumerator s := by
  have ha : AnalyticAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁.analyticAt _
  unfold zetaWindowNumerator
  exact ((analyticAt_const.mul analyticAt_id).sub analyticAt_const).sub (ha.deriv.div ha h)

private theorem zeta₁_eq_product {s : ℂ} (h : s ≠ 1) :
    riemannZeta₁ s = (s-1)*riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul h, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr h), one_mul]

private theorem zetaWindowTransform_eq_quotient {s : ℂ} (h : s ≠ 1) :
    zetaWindowTransform s = zetaWindowNumerator s / (s*(s-1)) := by
  rw [zetaWindowTransform, dslope_of_ne _ h, slope_def_field,
    zetaWindowNumerator_one, sub_zero, div_div, mul_comm (s-1)]

theorem zetaWindowTransform_differentiableAt {s : ℂ} (hs : 0 < s.re)
    (hζ : riemannZeta s ≠ 0) : DifferentiableAt ℂ zetaWindowTransform s := by
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos hs
  have hnum : DifferentiableAt ℂ (dslope zetaWindowNumerator 1) s := by
    rcases eq_or_ne s 1 with rfl | h
    · exact (analyticAt_dslope_of_analyticAt
        (zetaWindowNumerator_analytic (by simp))).differentiableAt
    · refine (differentiableAt_dslope_of_ne h).mpr (zetaWindowNumerator_analytic ?_).differentiableAt
      rw [zeta₁_eq_product h]
      exact mul_ne_zero (sub_ne_zero.mpr h) hζ
  unfold zetaWindowTransform
  exact hnum.div differentiableAt_id hs₀

/-- Away from its poles this is the usual Mellin transform expression. -/
theorem zetaWindowTransform_eq_logDerivative {s : ℂ} (hs : 1 < s.re) :
    zetaWindowTransform s =
      -(deriv riemannZeta s / riemannZeta s)/(s*(s-1)) -
      1/(s-1)^2 + (1+(Real.eulerMascheroniConstant:ℂ))/(s-1) := by
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hs₁ : s ≠ 1 := by intro h; simp [h] at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hloc : ∀ᶠ z : ℂ in 𝓝 s, z ≠ 1 := isOpen_ne.mem_nhds hs₁
  have he : riemannZeta₁ =ᶠ[𝓝 s] fun z => (z-1)*riemannZeta z :=
    hloc.mono (fun _ h => zeta₁_eq_product h)
  have hd : deriv riemannZeta₁ s = riemannZeta s + (s-1)*deriv riemannZeta s := by
    rw [he.deriv_eq]
    have hD : DifferentiableAt ℂ (fun z => z-(1:ℂ)) s := differentiableAt_id.sub_const _
    rw [deriv_fun_mul hD (differentiableAt_riemannZeta hs₁)]
    have heq : deriv (fun z => z-(1:ℂ)) s = 1 := by simpa using ((hasDerivAt_id s).sub_const (1:ℂ)).deriv
    rw [heq, one_mul]
  rw [zetaWindowTransform_eq_quotient hs₁, zetaWindowNumerator, zeta₁_eq_product hs₁, hd]
  field_simp [hs₀, sub_ne_zero.mpr hs₁, hz]
  ring

private theorem zeta₁_order_finite (ρ : ℂ) : analyticOrderAt riemannZeta₁ ρ ≠ ⊤ := by
  have h : AnalyticOnNhd ℂ riemannZeta₁ univ := fun s _ => differentiable_riemannZeta₁.analyticAt s
  exact h.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (1:ℂ)) (mem_univ ρ) (by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr (by simp : riemannZeta₁ 1 ≠ 0))]
      simp)

private theorem logDerived_eq_order_term {ρ : ℂ} (hρ : riemannZeta₁ ρ = 0) :
    ∃ (m : ℕ) (H : ℂ → ℂ), 0 < m ∧ AnalyticAt ℂ H ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv riemannZeta₁ s / riemannZeta₁ s = (m:ℂ)/(s-ρ) + H s := by
  have hAnalytic : AnalyticAt ℂ riemannZeta₁ ρ := differentiable_riemannZeta₁.analyticAt _
  obtain ⟨F,hF,hFρ,hFactor⟩ := hAnalytic.analyticOrderAt_ne_top.mp (zeta₁_order_finite ρ)
  let m := analyticOrderNatAt riemannZeta₁ ρ
  have hm : 0 < m := by
    have hn := hAnalytic.analyticOrderAt_ne_zero.mpr hρ
    rw [← Nat.cast_analyticOrderNatAt (zeta₁_order_finite ρ)] at hn
    by_contra! h
    apply hn
    change (m:ℕ∞) = 0
    rw [Nat.eq_zero_of_le_zero h, Nat.cast_zero]
  let H := fun s : ℂ => deriv F s / F s
  refine ⟨m,H,hm,hF.deriv.div hF hFρ,?_⟩
  have hFact : riemannZeta₁ =ᶠ[𝓝 ρ] fun s => (s-ρ)^m*F s :=
    hFactor.mono (fun _ h => by simpa only [smul_eq_mul] using h)
  have hLoc : ∀ᶠ s : ℂ in 𝓝 ρ, riemannZeta₁ =ᶠ[𝓝 s] fun z => (z-ρ)^m*F z :=
    eventually_eventually_nhds.mpr hFact
  have hFnear : ∀ᶠ s in 𝓝 ρ, F s ≠ 0 := hF.continuousAt.eventually_ne hFρ
  have ha := hF.eventually_analyticAt
  filter_upwards [hLoc.filter_mono nhdsWithin_le_nhds, hFnear.filter_mono nhdsWithin_le_nhds,
    ha.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin] with s hs hFn hAn hsρ
  have hs' : s ≠ ρ := hsρ
  have hdiff : HasDerivAt (fun z : ℂ => (z-ρ)^m) ((m:ℂ)*(s-ρ)^(m-1)) s := by
    have he := (hasDerivAt_pow m (s-ρ)).comp s ((hasDerivAt_id s).sub_const ρ)
    simpa only [Function.comp_def, id_eq, mul_one] using he
  have hequiv : (s-ρ)^m = (s-ρ)^(m-1)*(s-ρ) := by
    conv_lhs => rw [show m = (m-1)+1 by omega, pow_succ]
  rw [hs.deriv_eq, hs.self_of_nhds]
  change deriv ((fun z : ℂ => (z-ρ)^m) * F) s / ((s-ρ)^m * F s) = _
  rw [(hdiff.mul hAn.differentiableAt.hasDerivAt).deriv]
  change (((m:ℂ)*(s-ρ)^(m-1))*F s+(s-ρ)^m*deriv F s)/((s-ρ)^m*F s) =
    (m:ℂ)/(s-ρ)+deriv F s / F s
  rw [hequiv]
  field_simp [hFn, sub_ne_zero.mpr hs', pow_ne_zero _ (sub_ne_zero.mpr hs')]

theorem zetaWindowTransform_has_simplePole {ρ : ℂ} (hρ : 0 < ρ.re) (hζ : riemannZeta ρ = 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ F : ℂ → ℂ, AnalyticAt ℂ F ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, zetaWindowTransform s = c/(s-ρ)+F s := by
  have hρ₀ : ρ ≠ 0 := ne_zero_of_re_pos hρ
  have hρ₁ : ρ ≠ 1 := fun e => riemannZeta_one_ne_zero (e ▸ hζ)
  have hzρ : riemannZeta₁ ρ = 0 := by simp [zeta₁_eq_product hρ₁, hζ]
  obtain ⟨m,H,hm,hH,hmH⟩ := logDerived_eq_order_term hzρ
  let b (s : ℂ) := 1/(s*(s-1))
  have hb : AnalyticAt ℂ b ρ := analyticAt_const.div
    (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
    (mul_ne_zero hρ₀ (sub_ne_zero.mpr hρ₁))
  let c := -(m:ℂ)*b ρ
  have hc : c ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hm.ne'))
      (one_div_ne_zero (mul_ne_zero hρ₀ (sub_ne_zero.mpr hρ₁)))
  let F (s : ℂ) := (((1+(Real.eulerMascheroniConstant:ℂ))*s-1)-H s)*b s -
    (m:ℂ)*dslope b ρ s
  have hf : AnalyticAt ℂ F ρ :=
    (((analyticAt_const.mul analyticAt_id).sub analyticAt_const).sub hH).mul hb |>.sub
      (analyticAt_const.mul (analyticAt_dslope_of_analyticAt hb))
  refine ⟨c,hc,F,hf,?_⟩
  have hnear₁ : ∀ᶠ s : ℂ in 𝓝 ρ, s ≠ 1 := isOpen_ne.mem_nhds hρ₁
  filter_upwards [hmH,hnear₁.filter_mono nhdsWithin_le_nhds,eventually_mem_nhdsWithin] with s hs hs₁ hsρ
  have hs' : s ≠ ρ := hsρ
  rw [zetaWindowTransform_eq_quotient hs₁, zetaWindowNumerator, hs]
  dsimp [c,F]
  rw [dslope_of_ne _ hs', slope_def_field]
  simp only [b, div_eq_mul_inv, one_mul]
  ring

theorem riemannZeta_no_real_zero_in_positive_half {ρ : ℂ} (hρ : 0 < ρ.re) (hρi : ρ.im = 0) :
    riemannZeta ρ ≠ 0 := by
  by_cases h₁ : ρ = 1
  · simpa [h₁] using riemannZeta_one_ne_zero
  · intro hζ
    have he : ((ρ.re:ℝ):ℂ) = ρ := by apply Complex.ext <;> simp [hρi]
    have hn := XiPairingPublished.concrete_xi_no_real_zeros ρ.re
    rw [he] at hn
    have hz := EtaQBridgePublished.concrete_xi_bridge.2.2 ρ hρ h₁
    rw [hζ, mul_zero, zero_div] at hz
    exact hn (by rw [add_comm]; exact hz)

end MasulloAlpoge

set_option autoImplicit false

open ArithmeticFunction Complex Filter Finset Set MeasureTheory Topology

namespace MasulloAlpoge

private noncomputable def rampWeight (n : ℕ) (x : ℝ) : ℝ := max (x/(n:ℝ)-1) 0

/-- The corrected, ramp-smoothed von Mangoldt sum at modulus one. -/
noncomputable def zetaRampError (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (⌊x⌋₊+1), vonMangoldt n * rampWeight n x) -
    x*(Real.log x-1-Real.eulerMascheroniConstant)

private theorem rampWeight_zero_off_range {n : ℕ} {x : ℝ} (h : n ∉ Finset.range (⌊x⌋₊+1)) :
    rampWeight n x = 0 := by
  have hn : ⌊x⌋₊+1 ≤ n := by simpa using h
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx : x ≤ (n:ℝ) := (Nat.lt_floor_add_one x).le.trans (by exact_mod_cast hn)
  unfold rampWeight
  exact max_eq_right (sub_nonpos.mpr ((div_le_one hn₀).mpr hx))

private theorem zetaRamp_sum_eq_tsum (x : ℝ) :
    (∑ n ∈ Finset.range (⌊x⌋₊+1), vonMangoldt n * rampWeight n x) =
      ∑' n : ℕ, vonMangoldt n * rampWeight n x := by
  symm
  exact tsum_eq_sum (fun n hn => by rw [rampWeight_zero_off_range hn, mul_zero])

theorem zetaRampError_measurable : Measurable zetaRampError := by
  unfold zetaRampError
  simp_rw [zetaRamp_sum_eq_tsum]
  apply Measurable.sub
  · apply Measurable.tsum
    intro n
    unfold rampWeight
    fun_prop
  · have hl := Real.measurable_log
    fun_prop

private theorem vonMangoldt_le_nat (n : ℕ) : vonMangoldt n ≤ (n:ℝ) :=
  vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg n))

theorem zetaRampError_growth :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → |zetaRampError x| ≤ K*x^2 := by
  let γ := Real.eulerMascheroniConstant
  refine ⟨4+|γ|, by positivity, fun x hx => ?_⟩
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have h₁ (n : ℕ) : 0 ≤ vonMangoldt n * rampWeight n x :=
    mul_nonneg vonMangoldt_nonneg (le_max_right _ _)
  have h₂ (n : ℕ) : vonMangoldt n * rampWeight n x ≤ x := by
    by_cases hn : n = 0
    · subst n
      simpa using hx₀
    · have hpos : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hnon : 0 ≤ x/(n:ℝ) := div_nonneg hx₀ hpos.le
      have hl : rampWeight n x ≤ x/(n:ℝ) := max_le (by linarith) hnon
      calc
        _ ≤ (n:ℝ)*(x/(n:ℝ)) :=
          mul_le_mul (vonMangoldt_le_nat n) hl (le_max_right _ _) hpos.le
        _ = x := by field_simp
  have hf : (⌊x⌋₊:ℝ) ≤ x := Nat.floor_le hx₀
  let S := ∑ n ∈ Finset.range (⌊x⌋₊+1), vonMangoldt n * rampWeight n x
  have hS0 : 0 ≤ S := sum_nonneg fun n _ => h₁ n
  have hS : S ≤ 2*x^2 := by
    calc
      S ≤ ∑ n ∈ Finset.range (⌊x⌋₊+1), x := sum_le_sum fun n _ => h₂ n
      _ = ((⌊x⌋₊:ℝ)+1)*x := by simp [Nat.cast_add]
      _ ≤ (x+1)*x := mul_le_mul_of_nonneg_right (add_le_add hf le_rfl) hx₀
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) hx₀]
  have hL : |Real.log x - 1 - γ| ≤ x+1+|γ| := by
    calc
      _ ≤ |Real.log x-1|+|γ| := abs_sub _ _
      _ ≤ (|Real.log x|+|1|)+|γ| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ _ := by
        rw [abs_one, abs_of_nonneg (Real.log_nonneg hx)]
        exact add_le_add (add_le_add (Real.log_le_self hx₀) le_rfl) le_rfl
  have hmain : |x*(Real.log x-1-γ)| ≤ (2+|γ|)*x^2 := by
    rw [abs_mul, abs_of_nonneg hx₀]
    calc
      _ ≤ x*(x+1+|γ|) := mul_le_mul_of_nonneg_left hL hx₀
      _ ≤ x*(x+x+|γ| * x) := by
        gcongr
        exact le_mul_of_one_le_right (abs_nonneg γ) hx
      _ = _ := by ring
  change |S-x*(Real.log x-1-γ)| ≤ (4+|γ|)*x^2
  calc
    _ ≤ |S|+|x*(Real.log x-1-γ)| := abs_sub _ _
    _ ≤ 2*x^2+(2+|γ|)*x^2 := add_le_add (by simpa [abs_of_nonneg hS0] using hS) hmain
    _ = _ := by ring

private noncomputable def rampLaplaceTerm (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (rampWeight n (Real.exp u) : ℂ) * Complex.exp (-s*(u:ℂ))

private theorem rampLaplaceTerm_zero (s : ℂ) : rampLaplaceTerm 0 s = 0 := by
  funext u
  simp [rampLaplaceTerm, rampWeight]

private theorem rampLaplaceTerm_integrable {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    IntegrableOn (rampLaplaceTerm n s) (Ioi 0) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [rampLaplaceTerm_zero]
    exact integrable_zero ℝ ℂ ((volume : Measure ℝ).restrict (Ioi 0))
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hdec : 1-s.re < 0 := by linarith
  have hi := (integrableOn_exp_mul_Ioi hdec 0).const_mul ((n:ℝ)⁻¹)
  have hmeas : Measurable (rampLaplaceTerm n s) := by unfold rampLaplaceTerm rampWeight; fun_prop
  refine hi.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  have he : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  have hle : rampWeight n (Real.exp u) ≤ Real.exp u/(n:ℝ) :=
    max_le (by linarith) (by positivity)
  have hh : 0 ≤ rampWeight n (Real.exp u) := le_max_right _ _
  change ‖rampLaplaceTerm n s u‖ ≤ (n:ℝ)⁻¹*Real.exp ((1-s.re)*u)
  rw [rampLaplaceTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh, Complex.norm_exp, he]
  calc
    _ ≤ (Real.exp u/(n:ℝ)) * Real.exp (-s.re*u) :=
      mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
    _ = (n:ℝ)⁻¹*(Real.exp u*Real.exp (-s.re*u)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem rampLaplaceTerm_integral {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (0:ℝ), rampLaplaceTerm n s u) = (n:ℂ)^(-s)/(s*(s-1)) := by
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn₁ : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let l := Real.log (n:ℝ)
  have hl : 0 ≤ l := Real.log_nonneg (by exact_mod_cast hn)
  have hr : (-(s-1)).re < 0 := by simp [Complex.sub_re]; linarith
  have hr' : (-s).re < 0 := by simp; linarith
  let F (u : ℝ) := (n:ℂ)⁻¹*Complex.exp (-(s-1)*(u:ℂ))-Complex.exp (-s*(u:ℂ))
  have he : rampLaplaceTerm n s = (Ioi l).indicator F := by
    funext u
    by_cases hu : u ∈ Ioi l
    · have hx : (n:ℝ) < Real.exp u := by
        simpa [l, Real.exp_log hn₀] using Real.exp_lt_exp.mpr hu
      have hw : 0 ≤ Real.exp u/(n:ℝ)-1 := sub_nonneg.mpr ((one_le_div hn₀).mpr hx.le)
      rw [indicator_of_mem hu, rampLaplaceTerm, rampWeight, max_eq_left hw]
      push_cast
      have h : Complex.exp (-(s-1)*(u:ℂ)) = Complex.exp (u:ℂ)*Complex.exp (-s*(u:ℂ)) := by
        rw [← Complex.exp_add]; congr 1; ring
      dsimp [F]
      rw [h]
      ring
    · have hx : Real.exp u ≤ (n:ℝ) := by
        have h : u ≤ l := le_of_not_gt hu
        simpa [l, Real.exp_log hn₀] using Real.exp_le_exp.mpr h
      rw [indicator_of_notMem hu, rampLaplaceTerm, rampWeight,
        max_eq_right (sub_nonpos.mpr ((div_le_one hn₀).mpr hx)), Complex.ofReal_zero, zero_mul]
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hs₁ : s-1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  rw [he, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hl)]
  dsimp [F]
  rw [integral_sub ((integrableOn_exp_mul_complex_Ioi hr l).const_mul _)
    (integrableOn_exp_mul_complex_Ioi hr' l), integral_const_mul,
    integral_exp_mul_complex_Ioi hr, integral_exp_mul_complex_Ioi hr']
  have hcp : Complex.exp (-s*(l:ℂ)) = (n:ℂ)^(-s) := by
    rw [Complex.cpow_def_of_ne_zero hn₁, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn₀.le]
    dsimp [l]
    rw [mul_comm]
  have hex : Complex.exp (-(s-1)*(l:ℂ)) = Complex.exp (-s*(l:ℂ))*(n:ℂ) := by
    rw [show -(s-1)*(l:ℂ) = -s*(l:ℂ)+(l:ℂ) by ring, Complex.exp_add,
      ← Complex.ofReal_exp, show Real.exp l = (n:ℝ) by exact Real.exp_log hn₀,
      Complex.ofReal_natCast]
  rw [hex,hcp]
  field_simp [hs₀,hs₁,hn₁]
  ring

private theorem norm_rampLaplaceTerm_eq_real_cast (n : ℕ) (s : ℂ) (u : ℝ) :
    (‖rampLaplaceTerm n s u‖:ℂ) = rampLaplaceTerm n ((s.re:ℝ):ℂ) u := by
  have hre : (-s*(u:ℂ)).re = -s.re*u := by simp [Complex.mul_re]
  have h : 0 ≤ rampWeight n (Real.exp u) := le_max_right _ _
  simp only [rampLaplaceTerm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg h, Complex.norm_exp, hre]
  push_cast
  rfl

private theorem rampLaplaceTerm_integral_norm {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Ioi (0:ℝ), ‖rampLaplaceTerm n s u‖) =
      (n:ℝ)^(-s.re)/(s.re*(s.re-1)) := by
  apply Complex.ofReal_injective
  have hnorm : ((∫ u in Ioi (0:ℝ), ‖rampLaplaceTerm n s u‖ : ℝ) : ℂ) =
      ∫ u in Ioi (0:ℝ), rampLaplaceTerm n ((s.re:ℝ):ℂ) u := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => norm_rampLaplaceTerm_eq_real_cast n s u)
  rw [hnorm, rampLaplaceTerm_integral hn (by simpa : 1 < ((s.re:ℝ):ℂ).re)]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

private noncomputable def weightedRampTerm (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (vonMangoldt n : ℂ) * rampLaplaceTerm n s u

private theorem weightedRampTerm_integrable {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    IntegrableOn (weightedRampTerm n s) (Ioi 0) := (rampLaplaceTerm_integrable hs n).const_mul _

private theorem summable_weightedRamp_integral_norm {s : ℂ} (hs : 2 < s.re) :
    Summable (fun n : ℕ => ∫ u in Ioi (0:ℝ), ‖weightedRampTerm n s u‖) := by
  let D : ℝ := s.re*(s.re-1)
  have hσ : 1 < s.re := by linarith
  have hD : 0 < D := mul_pos (by linarith) (sub_pos.mpr hσ)
  have hsum : Summable (fun n : ℕ => ((n:ℝ)^(s.re-1))⁻¹ / D) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < s.re-1)).div_const _
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
    (fun n => ?_) hsum
  rcases eq_or_ne n 0 with rfl | hn
  · simp [weightedRampTerm, div_nonneg, inv_nonneg, Real.rpow_nonneg, hD.le]
  · rw [show (fun u => ‖weightedRampTerm n s u‖) =
        (fun u => vonMangoldt n * ‖rampLaplaceTerm n s u‖) by
      funext u
      rw [weightedRampTerm, norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]]
    rw [integral_const_mul, rampLaplaceTerm_integral_norm (Nat.pos_of_ne_zero hn) hσ]
    have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have h : (n:ℝ)*(n:ℝ)^(-s.re) = ((n:ℝ)^(s.re-1))⁻¹ := by
      conv_lhs => arg 1; rw [← Real.rpow_one (n:ℝ)]
      rw [← Real.rpow_add hn₀, ← Real.rpow_neg hn₀.le]
      congr 1
      ring
    calc
      _ ≤ (n:ℝ)*((n:ℝ)^(-s.re)/D) :=
        mul_le_mul_of_nonneg_right (vonMangoldt_le_nat n) (by positivity)
      _ = _ := by rw [← mul_div_assoc, h]

private theorem weightedRampTerm_integral {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    (∫ u in Ioi (0:ℝ), weightedRampTerm n s u) =
      LSeries.term (fun k => (vonMangoldt k:ℂ)) s n/(s*(s-1)) := by
  by_cases hn : n = 0
  · simp [hn, weightedRampTerm]
  · unfold weightedRampTerm
    rw [integral_const_mul, rampLaplaceTerm_integral (Nat.pos_of_ne_zero hn) hs,
      LSeries.term_of_ne_zero hn, Complex.cpow_neg]
    ring

private noncomputable def rampArithmeticSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊+1), vonMangoldt n * rampWeight n x

private theorem weightedRampTerm_tsum (s : ℂ) (u : ℝ) :
    (∑' n, weightedRampTerm n s u) =
      (rampArithmeticSum (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ)) := by
  rw [tsum_eq_sum (s := Finset.range (⌊Real.exp u⌋₊+1)) (by
    intro n hn
    rw [weightedRampTerm, rampLaplaceTerm, rampWeight_zero_off_range hn, Complex.ofReal_zero, zero_mul, mul_zero])]
  simp only [weightedRampTerm, rampLaplaceTerm, ← mul_assoc, ← sum_mul, rampArithmeticSum,
    Complex.ofReal_sum, Complex.ofReal_mul]

private theorem rampArithmetic_laplace {s : ℂ} (hs : 2 < s.re) :
    (∫ u in Ioi (0:ℝ), (rampArithmeticSum (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))) =
      -(deriv riemannZeta s/riemannZeta s)/(s*(s-1)) := by
  have hσ : 1 < s.re := by linarith
  have hc := hasSum_integral_of_summable_integral_norm
    (fun n => weightedRampTerm_integrable hσ n) (summable_weightedRamp_integral_norm hs)
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun u _ => weightedRampTerm_tsum s u)]
  rw [← hc.tsum_eq]
  simp_rw [weightedRampTerm_integral hσ]
  rw [tsum_div_const]
  change LSeries (fun k => (vonMangoldt k:ℂ)) s/(s*(s-1)) = _
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ]
  rw [neg_div]

/-- The real logarithmic ramp error has at most quadratic growth in the scale. -/
theorem zetaRampError_exp_growth :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u → |zetaRampError (Real.exp u)| ≤ K*Real.exp (2*u) := by
  obtain ⟨K,hK,h⟩ := zetaRampError_growth
  refine ⟨K,hK,fun u hu => ?_⟩
  have he : (Real.exp u)^2 = Real.exp (2*u) := by simpa using (Real.exp_nat_mul u 2).symm
  rw [← he]
  exact h _ (Real.one_le_exp hu)

private theorem exponential_const_integral {s : ℂ} (hs : 0 < s.re) :
    (∫ u in Ioi (0:ℝ), Complex.exp (-s*(u:ℂ))) = 1/s := by
  have h := integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  simpa [div_eq_mul_inv] using h

private theorem correction_integrable_and_integral {s : ℂ} (hs : 1 < s.re) :
    let F := fun u : ℝ => ((Real.exp u * (u-1-Real.eulerMascheroniConstant) : ℝ):ℂ) *
      Complex.exp (-s*(u:ℂ))
    IntegrableOn F (Ioi (0:ℝ)) ∧
      (∫ u in Ioi (0:ℝ), F u) = 1/(s-1)^2-(1+(Real.eulerMascheroniConstant:ℂ))/(s-1) := by
  let a := s-1
  have ha : 0 < a.re := by simp [a, Complex.sub_re, sub_pos, hs]
  let A (u : ℝ) := (u:ℂ)*Complex.exp (-a*(u:ℂ))
  let B (u : ℝ) := (1+(Real.eulerMascheroniConstant:ℂ))*Complex.exp (-a*(u:ℂ))
  have hF (u : ℝ) :
      ((Real.exp u * (u-1-Real.eulerMascheroniConstant) : ℝ):ℂ)*Complex.exp (-s*(u:ℂ)) =
        A u - B u := by
    dsimp [A,B,a]
    have he : Complex.exp (-(s-1)*(u:ℂ)) = Complex.exp (u:ℂ)*Complex.exp (-s*(u:ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [he]
    push_cast
    ring
  have hA : IntegrableOn A (Ioi 0) := linear_exponential_integrable ha
  have hB : IntegrableOn B (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0).const_mul _
  simp only [hF]
  refine ⟨hA.sub hB,?_⟩
  rw [integral_sub hA hB]
  dsimp [A,B]
  rw [integral_const_mul, linear_exponential_integral ha, exponential_const_integral ha]
  dsimp [a]
  ring

/-- Compute the modulus-one ramp transform in the half-plane of absolute
convergence. The two elementary terms are the exact pole correction. -/
theorem zetaRampError_laplace {s : ℂ} (hs : 2 < s.re) :
    (∫ u in Ioi (0:ℝ), (zetaRampError (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))) =
      -(deriv riemannZeta s/riemannZeta s)/(s*(s-1)) -
        1/(s-1)^2 + (1+(Real.eulerMascheroniConstant:ℂ))/(s-1) := by
  obtain ⟨K,hK,hG⟩ := zetaRampError_exp_growth
  have hi := laplace_integrable_of_exponential_bound
    (zetaRampError_measurable.comp Real.continuous_exp.measurable) hK hG hs
  let P (u : ℝ) := (rampArithmeticSum (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ))
  let Q (u : ℝ) := ((Real.exp u * (u-1-Real.eulerMascheroniConstant) : ℝ):ℂ) *
    Complex.exp (-s*(u:ℂ))
  obtain ⟨hQ,hQi⟩ := correction_integrable_and_integral (by linarith : 1 < s.re)
  have hQi' : (∫ u in Ioi (0:ℝ), Q u) = _ := hQi
  have hQ' : IntegrableOn Q (Ioi (0:ℝ)) := hQ
  have hEq (u : ℝ) : (zetaRampError (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ)) = P u-Q u := by
    simp only [zetaRampError, P, Q, rampArithmeticSum, Real.log_exp]
    push_cast
    ring
  have hi' : IntegrableOn (fun u => P u-Q u) (Ioi (0:ℝ)) := by
    have he : (fun u : ℝ => ((zetaRampError ∘ Real.exp) u:ℂ)*Complex.exp (-s*(u:ℂ))) =
        (fun u => P u-Q u) := funext hEq
    rwa [he] at hi
  have hP : IntegrableOn P (Ioi (0:ℝ)) := by
    have h := hi'.add hQ'
    have he : (fun u => P u-Q u)+Q = P := by
      funext u
      simp
    rwa [he] at h
  have hPi : (∫ u in Ioi (0:ℝ), P u) = -(deriv riemannZeta s/riemannZeta s)/(s*(s-1)) :=
    rampArithmetic_laplace hs
  calc
    _ = ∫ u in Ioi (0:ℝ), P u-Q u := setIntegral_congr_fun measurableSet_Ioi (fun u _ => hEq u)
    _ = _ := by rw [integral_sub hP hQ', hPi, hQi']; ring

/-- A relative scale window becomes a relative interval in the logarithmic coordinate. -/
theorem upper_windows_in_log_coordinate {θ C δ : ℝ}
    (h : ∀ X : ℝ, ∃ Y : ℝ, X ≤ Y ∧ ∀ x ∈ Icc Y (Y^(1+δ)), zetaRampError x ≤ C*x^θ) :
    ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∀ u ∈ Icc U ((1+δ)*U),
      zetaRampError (Real.exp u) ≤ C*Real.exp (θ*u) := by
  intro U₀
  obtain ⟨Y,hY,hWin⟩ := h (Real.exp U₀)
  have hY₀ := (Real.exp_pos U₀).trans_le hY
  let U := Real.log Y
  have hu₀ : U₀ ≤ U := by
    exact (Real.le_log_iff_exp_le hY₀).mpr hY
  refine ⟨U,hu₀,fun u hu => ?_⟩
  have hLo : Y ≤ Real.exp u := by
    rw [← Real.exp_log hY₀]
    exact Real.exp_le_exp.mpr hu.1
  have hHi : Real.exp u ≤ Y^(1+δ) := by
    rw [Real.rpow_def_of_pos hY₀]
    exact Real.exp_le_exp.mpr (by simpa [U, mul_comm] using hu.2)
  have h := hWin _ ⟨hLo,hHi⟩
  simpa [Real.exp_mul, mul_comm θ] using h

end MasulloAlpoge

set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory

namespace MasulloAlpoge

/-- One-sided upper bounds for the original zeta ramp on arbitrarily late
relative scale intervals exclude zeros to their right. -/
theorem zeta_ne_zero_to_right_of_upper_windows {θ δ C : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ) (hC : 0 ≤ C)
    (h : ∀ X : ℝ, ∃ Y : ℝ, X ≤ Y ∧ ∀ y ∈ Icc Y (Y^(1+δ)), zetaRampError y ≤ C*y^θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  let Z := riemannZetaZeros ∩ {z : ℂ | θ ≤ z.re}
  have hZ : IsClosed Z := isClosed_riemannZetaZeros.inter (isClosed_le continuous_const Complex.continuous_re)
  have hZd : IsDiscrete Z := isDiscrete_riemannZetaZeros.mono inter_subset_left
  have hIm (z : ℂ) (hz : z ∈ Z) : z.im ≠ 0 := by
    intro hi
    exact (riemannZeta_no_real_zero_in_positive_half (hθ.trans_le hz.2) hi)
      (mem_riemannZetaZeros.mp hz.1)
  have hRe (z : ℂ) (hz : z ∈ Z) : z.re ≤ 2 := by
    by_contra! hg
    exact (riemannZeta_ne_zero_of_one_le_re (by linarith : 1 ≤ z.re)) (mem_riemannZetaZeros.mp hz.1)
  have hdiff (s : ℂ) (hs : θ < s.re) (hz : s ∉ Z) :
      DifferentiableAt ℂ zetaWindowTransform s := by
    apply zetaWindowTransform_differentiableAt (hθ.trans hs)
    intro he
    exact hz ⟨mem_riemannZetaZeros.mpr he, hs.le⟩
  have hP (ρ : ℂ) (hρ : ρ ∈ Z) :
      ∃ c : ℂ, c ≠ 0 ∧ ∃ F : ℂ → ℂ, AnalyticAt ℂ F ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, zetaWindowTransform s = c/(s-ρ)+F s :=
    zetaWindowTransform_has_simplePole (hθ.trans_le hρ.2) (mem_riemannZetaZeros.mp hρ.1)
  obtain ⟨K,hK,hgrowth⟩ := zetaRampError_exp_growth
  have hPhi (s : ℂ) (hs : 2 < s.re) :
      zetaWindowTransform s =
        ∫ u in Ioi (0:ℝ), (zetaRampError (Real.exp u):ℂ)*Complex.exp (-s*(u:ℂ)) := by
    rw [zetaWindowTransform_eq_logDerivative (by linarith : 1 < s.re), zetaRampError_laplace hs]
  have hZ' := no_nonreal_poles_of_upper_windows hZ hZd hIm
    (zetaRampError_measurable.comp Real.continuous_exp.measurable)
    hK hC (by linarith : θ ≤ 2) hδ hgrowth (upper_windows_in_log_coordinate h)
    hPhi hRe hdiff hP
  intro s hs hz
  exact (not_le_of_gt hs) (hZ' s ⟨mem_riemannZetaZeros.mpr hz, hs.le⟩)

theorem zero_free_right_of_zeta_upper_windows
    (h : ∀ θ : ℝ, 1/2 < θ → θ < 1 → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ X : ℝ, 1 ≤ X → ∃ Y : ℝ, X ≤ Y ∧
        ∀ y ∈ Icc Y (Y^(1+δ)), zetaRampError y ≤ C*y^θ)
    (s : ℂ) (hs : 1/2 < s.re) :
    riemannZeta s ≠ 0 := by
  by_cases h₁ : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h₁
  let θ := (1/2+s.re)/2
  have ht₀ : 1/2 < θ := by dsimp [θ]; linarith
  have ht₁ : θ < 1 := by dsimp [θ]; linarith
  have ht₂ : θ < s.re := by dsimp [θ]; linarith
  obtain ⟨δ,C,hδ,hC,hwin⟩ := h θ ht₀ ht₁
  apply zeta_ne_zero_to_right_of_upper_windows (by linarith) ht₁ hδ hC _ s ht₂
  intro X
  obtain ⟨Y,hY,hw⟩ := hwin (max 1 X) (le_max_left _ _)
  exact ⟨Y,(le_max_right _ _).trans hY,hw⟩

end MasulloAlpoge

theorem MasulloRH.zero_free_right (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (_hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  apply MasulloAlpoge.zero_free_right_of_zeta_upper_windows _ s hs
  simpa only [MasulloAlpoge.zetaRampError, MasulloAlpoge.rampWeight] using
    MasulloRH.smoothed_prime_ramp_upper_windows

end

-- Step 3: `MasulloRH.zero_free_right` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis := by
  have hright : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
    fun s hs hs1 => MasulloRH.zero_free_right s hs hs1
  refine riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => ?_)
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hneg : ∀ n : ℕ, s ≠ -(n : ℂ) := fun n h => by
      have hre := congrArg Complex.re h
      simp at hre
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hneg hs1
    rw [hz, mul_zero] at hfe
    have hre : (1 / 2 : ℝ) < (1 - s).re := by simp; linarith
    have h1s : (1 - s) ≠ 1 := fun h => by
      have hre' := congrArg Complex.re h
      simp at hre'
      linarith
    exact hright (1 - s) hre h1s hfe
  · exact heq
  · exact absurd hz (hright s hgt hs1)

end
