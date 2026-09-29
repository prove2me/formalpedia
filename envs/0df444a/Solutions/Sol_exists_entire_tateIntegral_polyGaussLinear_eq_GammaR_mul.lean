-- Prove2me | solution 1 for exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ce940811-9ad5-5c92-83f8-73bb0ff4f928

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Data.Real.Sign
import Theorems.Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Order.Group.Lattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul

set_option autoImplicit false

section MellinAndStrip
open MeasureTheory Set Filter Topology

namespace MellinByParts

private theorem smul_div_cast (g : ℝ → ℂ) (u : ℝ) (hu : 0 < u) :
    ((u ^ 2)⁻¹ : ℝ) • (g u⁻¹ / ((u⁻¹ : ℝ) : ℂ)) = g u⁻¹ / (u : ℂ) := by
  simp only [Complex.real_smul]
  have hu0' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  push_cast
  field_simp

private theorem tendsto_zero_atTop {g g' : ℝ → ℂ} (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (g' x) x)
    (hg' : IntegrableOn g' (Ioi 0)) (hg : IntegrableOn (fun y => g y / y) (Ioi 0)) :
    Tendsto g atTop (𝓝 0) := by
  have hL := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi hderiv hg'
  set L := limUnder atTop g
  by_contra hne
  have hL0 : L ≠ 0 := by
    rintro h
    exact hne (h ▸ hL)
  have hpos : 0 < ‖L‖ / 2 := by
    have := norm_pos_iff.2 hL0
    linarith
  have hev : ∀ᶠ y in atTop, ‖L‖ / 2 ≤ ‖g y‖ := by
    have h1 : ∀ᶠ y in atTop, ‖g y - L‖ < ‖L‖ / 2 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hL).eventually (gt_mem_nhds hpos)
      exact this
    filter_upwards [h1] with y hy
    have := norm_sub_norm_le L (g y)
    rw [norm_sub_rev] at hy
    linarith
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop (1 : ℝ)))
  have hT1 : 1 ≤ T := (hT T le_rfl).2
  have hint : IntegrableOn (fun y : ℝ => ‖L‖ / 2 * y⁻¹) (Ioi T) := by
    refine Integrable.mono' ((hg.mono_set (Ioi_subset_Ioi (by linarith))).norm) ?_ ?_
    · exact (measurable_const.mul measurable_inv).aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun y hy => ?_
      have hTy : T ≤ y := le_of_lt hy
      have hy0 : 0 < y := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy0, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (hT y hTy).1 hy0.le
  have hint' : IntegrableOn (fun y : ℝ => y⁻¹) (Ioi T) := by
    refine IntegrableOn.congr_fun (hint.const_mul (‖L‖ / 2)⁻¹) (fun y _ => ?_) measurableSet_Ioi
    show (‖L‖ / 2)⁻¹ * (‖L‖ / 2 * y⁻¹) = y⁻¹
    field_simp
  exact not_integrableOn_Ioi_inv hint'

private theorem tendsto_zero_nhdsGT {g g' : ℝ → ℂ} (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (g' x) x)
    (hg' : IntegrableOn g' (Ioi 0)) (hg : IntegrableOn (fun y => g y / y) (Ioi 0)) :
    Tendsto g (𝓝[>] 0) (𝓝 0) := by
  have hderiv' : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (fun u : ℝ => g u⁻¹) ((-(u ^ 2)⁻¹) • g' u⁻¹) u :=
    fun u hu => (hderiv u⁻¹ (Set.mem_Ioi.2 (inv_pos.2 hu))).scomp u (hasDerivAt_inv (ne_of_gt hu))
  have A : IntegrableOn (fun u : ℝ => (-(u ^ 2)⁻¹) • g' u⁻¹) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_rpow_iff g' (p := (-1 : ℝ)) (by norm_num)).2 hg'
    refine h.neg.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu0 : (0 : ℝ) < u := hu
    simp only [Pi.neg_apply, abs_neg, abs_one, one_mul, Real.rpow_neg_one]
    rw [(by norm_num : (-1 : ℝ) - 1 = -(2 : ℝ)), Real.rpow_neg hu0.le, Real.rpow_two]
    exact (neg_smul _ _).symm
  have B : IntegrableOn (fun u : ℝ => g u⁻¹ / u) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_rpow_iff (fun y => g y / y) (p := (-1 : ℝ)) (by norm_num)).2 hg
    refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu0 : (0 : ℝ) < u := hu
    simp only [abs_neg, abs_one, one_mul, Real.rpow_neg_one]
    rw [(by norm_num : (-1 : ℝ) - 1 = -(2 : ℝ)), Real.rpow_neg hu0.le, Real.rpow_two]
    exact smul_div_cast g u hu0
  have hinf := tendsto_zero_atTop hderiv' A B
  have := hinf.comp tendsto_inv_nhdsGT_zero
  simpa [Function.comp_def, inv_inv] using this

private theorem half {f f₁ w : ℝ → ℂ} {c : ℂ}
    (hf : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt f (f₁ y / y) y) (hw : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt w (c * w y / y) y)
    (hfw : IntegrableOn (fun y => f y * w y) (Ioi 0)) (hf₁w : IntegrableOn (fun y => f₁ y * w y) (Ioi 0)) :
    (c + 1) * ∫ y in Ioi 0, f y * w y = -∫ y in Ioi 0, f₁ y * w y := by
  set G : ℝ → ℂ := fun y => f y * w y * y with hGdef
  set G' : ℝ → ℂ := fun y => f₁ y * w y + (c + 1) * (f y * w y) with hG'def
  have hG : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt G (G' y) y := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hy)
    have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      have h__af := (Complex.ofRealCLM.hasDerivAt (x := y))
      simp at h__af
      exact h__af
    have h := ((hf y hy).mul (hw y hy)).mul hid
    refine h.congr_deriv ?_
    simp only [hG'def, Pi.mul_apply]
    field_simp
    ring
  have hG'int : IntegrableOn G' (Ioi 0) := hf₁w.add (hfw.const_mul (c + 1))
  have hGdiv : IntegrableOn (fun y => G y / y) (Ioi 0) := by
    refine hfw.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hy)
    simp only [hGdef]
    field_simp
  have hinf : Tendsto G atTop (𝓝 0) := tendsto_zero_atTop hG hG'int hGdiv
  have h0 : Tendsto G (𝓝[>] 0) (𝓝 0) := tendsto_zero_nhdsGT hG hG'int hGdiv
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hG0]
    exact h0
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hG hG'int hinf
  rw [hG0, sub_zero] at key
  have hsplit : ∫ y in Ioi 0, G' y = (∫ y in Ioi 0, f₁ y * w y) + (c + 1) * ∫ y in Ioi 0, f y * w y := by
    simp only [hG'def]
    rw [integral_add hf₁w (hfw.const_mul (c + 1))]
    congr 1
    exact integral_const_mul (c + 1) _
  rw [hsplit] at key
  linear_combination key

private theorem whole {f f₁ w : ℝ → ℂ} {c : ℂ}
    (hf : ∀ y : ℝ, y ≠ 0 → HasDerivAt f (f₁ y / y) y) (hw : ∀ y : ℝ, y ≠ 0 → HasDerivAt w (c * w y / y) y)
    (hfw : Integrable (fun y => f y * w y)) (hf₁w : Integrable (fun y => f₁ y * w y)) :
    (c + 1) * ∫ y, f y * w y = -∫ y, f₁ y * w y := by
  have hp := half (fun y hy => hf y (ne_of_gt hy)) (fun y hy => hw y (ne_of_gt hy)) hfw.integrableOn
    hf₁w.integrableOn
  have hn := half (f := fun y => f (-y)) (f₁ := fun y => f₁ (-y)) (w := fun y => w (-y)) (c := c)
    (fun y hy => by
      have hy' : -y ≠ 0 := neg_ne_zero.2 (ne_of_gt hy)
      have h := (hf (-y) hy').scomp y (hasDerivAt_neg y)
      refine h.congr_deriv ?_
      have : ((-y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy'
      push_cast at this ⊢
      rw [neg_one_smul, div_neg, neg_neg])
    (fun y hy => by
      have hy' : -y ≠ 0 := neg_ne_zero.2 (ne_of_gt hy)
      have h := (hw (-y) hy').scomp y (hasDerivAt_neg y)
      refine h.congr_deriv ?_
      have : ((-y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy'
      push_cast at this ⊢
      rw [neg_one_smul, div_neg, neg_neg])
    (hfw.comp_neg.integrableOn) (hf₁w.comp_neg.integrableOn)
  have split : ∀ F : ℝ → ℂ, Integrable F → ∫ y, F y = (∫ y in Ioi 0, F y) + ∫ y in Ioi 0, F (-y) := by
    intro F hF
    rw [← intervalIntegral.integral_Iic_add_Ioi hF.integrableOn hF.integrableOn (b := 0), add_comm,
      integral_comp_neg_Ioi]
    simp [integral_Iic_eq_integral_Iio]
  rw [split _ hfw, split _ hf₁w, mul_add, hp, hn]
  ring

end MellinByParts

end MellinAndStrip

open MeasureTheory Complex in
private theorem gaussMoment_Ioi {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : 0 < w.re) :
    ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (w - 1) * (Real.exp (-(b * x ^ 2)) : ℂ) =
      (1 / 2 : ℂ) * (b : ℂ) ^ (-w / 2) * Gamma (w / 2) := by
  have hmel : (∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (w - 1) * (Real.exp (-(b * x ^ 2)) : ℂ)) =
      mellin (fun t : ℝ => ((Real.exp (-(b * t ^ (2 : ℝ))) : ℝ) : ℂ)) w := by
    simp only [mellin, smul_eq_mul, Real.rpow_two]
  have h2 := mellin_comp_rpow (fun u : ℝ => ((Real.exp (-(b * u)) : ℝ) : ℂ)) w (2 : ℝ)
  have h3 := mellin_comp_mul_left (fun v : ℝ => ((Real.exp (-v) : ℝ) : ℂ)) (w / 2) hb
  beta_reduce at h3
  simp only [Complex.ofReal_ofNat] at h2
  rw [hmel, h2, h3, ← GammaIntegral_eq_mellin, ← Gamma_eq_integral (by simpa using half_pos hw)]
  rw [show (-w / 2 : ℂ) = -(w / 2) by ring]
  rw [smul_eq_mul, ← Complex.coe_smul, smul_eq_mul, abs_two]
  push_cast
  ring

namespace PolyGaussTate

open MeasureTheory Set

private noncomputable def evenProfile (m : ℕ) (b : ℝ) (z : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ m * (Real.exp (-(b * r ^ 2)) : ℂ) * (r : ℂ) ^ (z - 1)

private theorem evenProfile_measurable (m : ℕ) (b : ℝ) (z : ℂ) : Measurable (evenProfile m b z) := by
  unfold evenProfile
  refine ((Complex.measurable_ofReal.pow_const m).mul ?_).mul (Complex.measurable_ofReal.pow_const (z - 1))
  exact Complex.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    ((measurable_const.mul (measurable_id.pow_const 2)).neg))

private theorem norm_evenProfile_of_pos (m : ℕ) (b : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ‖evenProfile m b z r‖ = r ^ ((m : ℝ) + z.re - 1) * Real.exp (-(b * r ^ 2)) := by
  unfold evenProfile
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.sub_re, Complex.one_re,
    show ((m : ℝ) + z.re - 1) = (m : ℝ) + (z.re - 1) by ring, Real.rpow_add hr, Real.rpow_natCast]
  ring

private theorem integrableOn_evenProfile_Ioi (m : ℕ) {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (evenProfile m b z) (Ioi 0) := by
  have hs : (-1 : ℝ) < (m : ℝ) + z.re - 1 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  refine (integrableOn_rpow_mul_exp_neg_mul_sq hb hs).mono' ?_ ?_
  · exact (evenProfile_measurable m b z).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [norm_evenProfile_of_pos m b z hr]
    simp only [neg_mul]
    exact le_of_eq rfl

private theorem integral_evenProfile_Ioi (m : ℕ) {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) :
    ∫ r in Ioi (0 : ℝ), evenProfile m b z r =
      (1 / 2 : ℂ) * (b : ℂ) ^ (-(z + m) / 2) * Complex.Gamma ((z + m) / 2) := by
  have hw : 0 < (z + m).re := by simp only [Complex.add_re, Complex.natCast_re]; positivity
  rw [← gaussMoment_Ioi hb hw]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  unfold evenProfile
  rw [show z + m - 1 = (m : ℂ) + (z - 1) by ring, Complex.cpow_add _ _ hr0, Complex.cpow_natCast]
  ring

private noncomputable def tateMonomialFn (m δ : ℕ) (b : ℝ) (z : ℂ) (ρ : ℝ) : ℂ :=
  (ρ : ℂ) ^ m * (Real.exp (-(b * ρ ^ 2)) : ℂ) * (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)

private theorem tateMonomialFn_of_pos (m δ : ℕ) (b : ℝ) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    tateMonomialFn m δ b z ρ = evenProfile m b z ρ := by
  unfold tateMonomialFn evenProfile
  rw [Real.sign_of_pos hρ, abs_of_pos hρ]
  simp

private theorem tateMonomialFn_of_neg (m δ : ℕ) (b : ℝ) (z : ℂ) {ρ : ℝ} (hρ : ρ < 0) :
    tateMonomialFn m δ b z ρ = (-1) ^ (m + δ) * evenProfile m b z (-ρ) := by
  unfold tateMonomialFn evenProfile
  rw [Real.sign_of_neg hρ, abs_of_neg hρ]
  push_cast
  rw [neg_sq, pow_add, neg_pow (ρ : ℂ) m]
  ring_nf
  rw [show ((-1 : ℂ)) ^ (m * 2) = 1 by rw [mul_comm, pow_mul]; simp]
  ring

private theorem integral_tateMonomialFn (m δ : ℕ) {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) :
    ∫ ρ : ℝ, tateMonomialFn m δ b z ρ =
      (1 + (-1) ^ (m + δ)) *
        ((1 / 2 : ℂ) * (b : ℂ) ^ (-(z + m) / 2) * Complex.Gamma ((z + m) / 2)) := by
  have hIoi : IntegrableOn (tateMonomialFn m δ b z) (Ioi 0) :=
    (integrableOn_evenProfile_Ioi m hb hz).congr_fun
      (fun ρ hρ => (tateMonomialFn_of_pos m δ b z hρ).symm) measurableSet_Ioi

  have hneg : IntegrableOn (fun ρ : ℝ => evenProfile m b z (-ρ)) (Iio 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    have e : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simp_rw [Function.comp_def, neg_neg, neg_preimage, neg_Iio, neg_zero]
    exact integrableOn_evenProfile_Ioi m hb hz
  have hIio : IntegrableOn (tateMonomialFn m δ b z) (Iio 0) :=
    IntegrableOn.congr_fun (hneg.const_mul ((-1 : ℂ) ^ (m + δ)))
      (fun ρ hρ => (tateMonomialFn_of_neg m δ b z hρ).symm) measurableSet_Iio
  have hIic : IntegrableOn (tateMonomialFn m δ b z) (Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio (enorm_ne_top)).mpr hIio
  rw [← intervalIntegral.integral_Iic_add_Ioi hIic hIoi, integral_Iic_eq_integral_Iio,
    setIntegral_congr_fun measurableSet_Iio (fun ρ hρ => tateMonomialFn_of_neg m δ b z hρ),
    setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => tateMonomialFn_of_pos m δ b z hρ),
    integral_evenProfile_Ioi m hb hz]
  have hL : (∫ x in Iio (0 : ℝ), (-1 : ℂ) ^ (m + δ) * evenProfile m b z (-x)) =
      (-1 : ℂ) ^ (m + δ) * ∫ r in Ioi (0 : ℝ), evenProfile m b z r := by
    simp_rw [← smul_eq_mul]
    rw [integral_smul, ← integral_Iic_eq_integral_Iio, integral_comp_neg_Iic, neg_zero]
  rw [hL, integral_evenProfile_Ioi m hb hz]
  ring

p2m_open_scoped "Nat Set.Nat"

private def kk (j δ m : ℕ) : ℕ := (j + m - δ) / 2

private theorem two_mul_kk_le (j δ m : ℕ) : 2 * kk j δ m ≤ j + m := by
  unfold kk; omega

private noncomputable def eTerm (j δ : ℕ) (bi : ℝ) (β : ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  if Even (j + m + δ) then
    (-β) ^ m / (m ! : ℂ) * ((bi : ℂ) ^ kk j δ m) * (ascPochhammer ℂ (kk j δ m)).eval w
  else 0

private noncomputable def eMono (j δ : ℕ) (bi : ℝ) (β : ℂ) (w : ℂ) : ℂ := ∑' m : ℕ, eTerm j δ bi β m w

private theorem norm_ascPochhammer_eval_le (k : ℕ) (w : ℂ) :
    ‖(ascPochhammer ℂ k).eval w‖ ≤ (‖w‖ + k) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, norm_mul]
    have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h1 : ‖w + (k : ℂ)‖ ≤ ‖w‖ + ((k + 1 : ℕ) : ℝ) := by
      calc ‖w + (k : ℂ)‖ ≤ ‖w‖ + ‖(k : ℂ)‖ := norm_add_le _ _
        _ = ‖w‖ + k := by rw [Complex.norm_natCast]
        _ ≤ ‖w‖ + ((k + 1 : ℕ) : ℝ) := by linarith
    have h2 : (‖w‖ + k) ^ k ≤ (‖w‖ + ((k + 1 : ℕ) : ℝ)) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    calc ‖(ascPochhammer ℂ k).eval w‖ * ‖w + (k : ℂ)‖
        ≤ (‖w‖ + ((k + 1 : ℕ) : ℝ)) ^ k * (‖w‖ + ((k + 1 : ℕ) : ℝ)) :=
          mul_le_mul (ih.trans h2) h1 (norm_nonneg _) (by positivity)
      _ = (‖w‖ + ((k + 1 : ℕ) : ℝ)) ^ (k + 1) := by rw [pow_succ]

private theorem pow_le_factorial_mul_exp {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x + k) ^ k ≤ (k ! : ℝ) * (Real.exp x * Real.exp 1 ^ k) := by
  have h := Real.pow_div_factorial_le_exp (x := x + k) (by positivity) k
  rw [div_le_iff₀ (by positivity)] at h
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  simpa [mul_comm] using h

private theorem factorial_add_le_two_pow (j m : ℕ) : ((j + m)! : ℝ) ≤ (2 : ℝ) ^ (j + m) * (j ! : ℝ) * (m ! : ℝ) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial m j
  have hc : (m + j).choose j ≤ 2 ^ (m + j) := Nat.choose_le_two_pow _ _
  have : (j + m)! ≤ 2 ^ (j + m) * j ! * m ! := by
    rw [add_comm j m, ← h]
    calc (m + j).choose j * m ! * j ! ≤ 2 ^ (m + j) * m ! * j ! := by gcongr
      _ = 2 ^ (m + j) * j ! * m ! := by ring
  exact_mod_cast this

private theorem factorial_sq_le (k : ℕ) : ((k ! : ℝ)) ^ 2 ≤ ((2 * k)! : ℝ) := by
  have h : k ! * k ! ∣ (k + k)! := Nat.factorial_mul_factorial_dvd_factorial_add k k
  have h' : k ! * k ! ≤ (k + k)! := Nat.le_of_dvd (Nat.factorial_pos _) h
  rw [two_mul]; exact_mod_cast (by simpa [sq] using h' : k ! ^ 2 ≤ (k + k)!)

private noncomputable def maj (j δ : ℕ) (R Bi Be : ℝ) (m : ℕ) : ℝ :=
  Real.exp R * (Be ^ m / (m ! : ℝ)) * (Bi * Real.exp 1) ^ kk j δ m * ((kk j δ m)! : ℝ)

private theorem maj_nonneg (j δ : ℕ) {R Bi Be : ℝ} (hBi : 0 ≤ Bi) (hBe : 0 ≤ Be) (m : ℕ) : 0 ≤ maj j δ R Bi Be m := by
  unfold maj; positivity

private theorem norm_eTerm_le (j δ : ℕ) {R Bi Be bi : ℝ} {β : ℂ} (hbi : |bi| ≤ Bi) (hβ : ‖β‖ ≤ Be)
    (m : ℕ) {w : ℂ} (hw : ‖w‖ ≤ R) : ‖eTerm j δ bi β m w‖ ≤ maj j δ R Bi Be m := by
  have hR : 0 ≤ R := (norm_nonneg w).trans hw
  have hBe : 0 ≤ Be := (norm_nonneg β).trans hβ
  have hBi : 0 ≤ Bi := (abs_nonneg bi).trans hbi
  unfold eTerm
  split_ifs with hev
  · set k := kk j δ m with hk
    rw [norm_mul, norm_mul, norm_div, norm_pow, norm_neg, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs]
    have hP : ‖(ascPochhammer ℂ k).eval w‖ ≤ (k ! : ℝ) * (Real.exp R * Real.exp 1 ^ k) := by
      refine (norm_ascPochhammer_eval_le k w).trans ?_
      refine (pow_le_pow_left₀ (by positivity) (by linarith : ‖w‖ + k ≤ R + k) k).trans ?_
      exact pow_le_factorial_mul_exp hR k
    have h1 : ‖β‖ ^ m / (m ! : ℝ) ≤ Be ^ m / (m ! : ℝ) := by gcongr
    have h2 : |bi| ^ k ≤ Bi ^ k := pow_le_pow_left₀ (abs_nonneg bi) hbi k
    calc ‖β‖ ^ m / (m ! : ℝ) * |bi| ^ k * ‖(ascPochhammer ℂ k).eval w‖
        ≤ Be ^ m / (m ! : ℝ) * Bi ^ k * ((k ! : ℝ) * (Real.exp R * Real.exp 1 ^ k)) := by
          gcongr
      _ = maj j δ R Bi Be m := by unfold maj; rw [← hk, mul_pow]; ring
  · simp only [norm_zero]; exact maj_nonneg j δ hBi hBe m

private theorem maj_sq_le (j δ : ℕ) {R Bi Be : ℝ} (hBi : 1 ≤ Bi) (m : ℕ) :
    maj j δ R Bi Be m ^ 2 ≤
      (Real.exp R ^ 2 * (j ! : ℝ) * (2 * (Bi * Real.exp 1)) ^ j) *
        (Be ^ 2 * (2 * (Bi * Real.exp 1))) ^ m / (m ! : ℝ) := by
  set k := kk j δ m with hk
  have hkm : 2 * k ≤ j + m := two_mul_kk_le j δ m
  have hX : 1 ≤ Bi * Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  have hm : (0 : ℝ) < m ! := by positivity

  have hA : (Bi * Real.exp 1) ^ (2 * k) ≤ (Bi * Real.exp 1) ^ (j + m) := pow_le_pow_right₀ hX hkm
  have hB : ((k ! : ℝ)) ^ 2 ≤ (2 : ℝ) ^ (j + m) * (j ! : ℝ) * (m ! : ℝ) := by
    refine (factorial_sq_le k).trans ?_
    refine le_trans ?_ (factorial_add_le_two_pow j m)
    exact_mod_cast Nat.factorial_le hkm
  have hX0 : 0 ≤ Bi * Real.exp 1 := by positivity
  unfold maj
  rw [← hk]
  have expand : (Real.exp R * (Be ^ m / (m ! : ℝ)) * (Bi * Real.exp 1) ^ k * (k ! : ℝ)) ^ 2 =
      Real.exp R ^ 2 * (Be ^ 2) ^ m / (m ! : ℝ) ^ 2 * (Bi * Real.exp 1) ^ (2 * k) * ((k ! : ℝ)) ^ 2 := by
    rw [pow_mul']; ring
  rw [expand]
  calc Real.exp R ^ 2 * (Be ^ 2) ^ m / (m ! : ℝ) ^ 2 * (Bi * Real.exp 1) ^ (2 * k) * ((k ! : ℝ)) ^ 2
      ≤ Real.exp R ^ 2 * (Be ^ 2) ^ m / (m ! : ℝ) ^ 2 * (Bi * Real.exp 1) ^ (j + m) *
          ((2 : ℝ) ^ (j + m) * (j ! : ℝ) * (m ! : ℝ)) := by gcongr
    _ = (Real.exp R ^ 2 * (j ! : ℝ) * (2 * (Bi * Real.exp 1)) ^ j) *
          (Be ^ 2 * (2 * (Bi * Real.exp 1))) ^ m / (m ! : ℝ) := by
        field_simp
        ring

private theorem summable_maj (j δ : ℕ) {R Bi Be : ℝ} (hBi : 1 ≤ Bi) (hBe : 0 ≤ Be) :
    Summable (maj j δ R Bi Be) := by
  set C : ℝ := Real.exp R ^ 2 * (j ! : ℝ) * (2 * (Bi * Real.exp 1)) ^ j with hC
  set y : ℝ := Be ^ 2 * (2 * (Bi * Real.exp 1)) with hy
  have hC0 : 0 ≤ C := by positivity
  clear_value C y

  have hdom : ∀ m : ℕ, maj j δ R Bi Be m ≤ (C * (2 * y) ^ m / (m ! : ℝ) + (1 / 2 : ℝ) ^ m) / 2 := by
    intro m
    have ha0 : 0 ≤ maj j δ R Bi Be m := maj_nonneg j δ (by linarith) hBe m
    have hsq := maj_sq_le (R := R) (Be := Be) j δ hBi m
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have hamgm : maj j δ R Bi Be m ≤ (2 ^ m * maj j δ R Bi Be m ^ 2 + (1 / 2 : ℝ) ^ m) / 2 := by
      have hhalf : (1 / 2 : ℝ) ^ m = (2 ^ m)⁻¹ := by rw [one_div, inv_pow]
      rw [hhalf, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have := sq_nonneg (2 ^ m * maj j δ R Bi Be m - 1)
      have hinv : (2 ^ m : ℝ) * (2 ^ m)⁻¹ = 1 := mul_inv_cancel₀ h2m.ne'
      nlinarith [hinv, inv_pos.mpr h2m]
    refine hamgm.trans ?_
    have : 2 ^ m * maj j δ R Bi Be m ^ 2 ≤ C * (2 * y) ^ m / (m ! : ℝ) := by
      calc 2 ^ m * maj j δ R Bi Be m ^ 2 ≤ 2 ^ m * (C * y ^ m / (m ! : ℝ)) := by rw [hC, hy]; gcongr
        _ = C * (2 * y) ^ m / (m ! : ℝ) := by rw [mul_pow]; ring
    linarith
  refine Summable.of_nonneg_of_le (fun m => maj_nonneg j δ (by linarith) hBe m) hdom ?_
  refine Summable.div_const ?_ 2
  refine Summable.add ?_ summable_geometric_two
  have h := (Real.summable_pow_div_factorial (2 * y)).mul_left C
  simpa [mul_div_assoc] using h

private theorem differentiable_eMono (j δ : ℕ) (bi : ℝ) (β : ℂ) : Differentiable ℂ (eMono j δ bi β) := by
  intro w₀
  set R : ℝ := ‖w₀‖ + 1 with hR
  have hRpos : 0 ≤ R := by positivity
  have hU : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' m : ℕ, eTerm j δ bi β m w) (Metric.ball (0 : ℂ) R) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (summable_maj (R := R) j δ (le_max_right |bi| 1) (norm_nonneg β)) ?_ hU ?_
    · intro m
      unfold eTerm
      split_ifs
      · exact ((differentiable_const _).mul (Polynomial.differentiable _)).differentiableOn
      · exact differentiableOn_const 0
    · intro m w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact norm_eTerm_le j δ (le_max_left |bi| 1) le_rfl m hw.le
  have hmem : w₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, hR]; linarith
  exact (hdiff.differentiableAt (hU.mem_nhds hmem))

open Complex in

private theorem Gamma_add_nat_eq (k : ℕ) {w : ℂ} (hw : 0 < w.re) :
    Complex.Gamma (w + k) = Complex.Gamma w * (ascPochhammer ℂ k).eval w := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne : w + (k : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    rw [show w + ((k + 1 : ℕ) : ℂ) = (w + k) + 1 by push_cast; ring, Complex.Gamma_add_one _ hne, ih,
      ascPochhammer_succ_eval]
    ring

private theorem measurable_sign : Measurable Real.sign := by
  have : Real.sign = fun r : ℝ => if r < 0 then (-1 : ℝ) else if 0 < r then 1 else 0 := by
    funext r; rfl
  rw [this]
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  exact Measurable.ite measurableSet_Ioi measurable_const measurable_const

private theorem measurable_tateMonomialFn (m δ : ℕ) (b : ℝ) (z : ℂ) : Measurable (tateMonomialFn m δ b z) := by
  unfold tateMonomialFn
  refine (((Complex.measurable_ofReal.pow_const m).mul ?_).mul
    ((Complex.measurable_ofReal.comp measurable_sign).pow_const δ)).mul
    ((Complex.measurable_ofReal.comp measurable_abs).pow_const (z - 1))
  exact Complex.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    ((measurable_const.mul (measurable_id.pow_const 2)).neg))

private theorem integral_term_eq (j δ : ℕ) (hδ : δ ≤ 1) {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) (β : ℂ) (m : ℕ) :
    (-β) ^ m / (m ! : ℂ) * ∫ ρ : ℝ, tateMonomialFn (j + m) δ b z ρ =
      Complex.Gamma ((z + δ) / 2) * (b : ℂ) ^ (-((z + δ) / 2)) * eTerm j δ b⁻¹ β m ((z + δ) / 2) := by
  rw [integral_tateMonomialFn (j + m) δ hb hz]
  unfold eTerm
  split_ifs with hev
  ·
    obtain ⟨r, hr⟩ := hev
    have hk : j + m = 2 * kk j δ m + δ := by unfold kk; omega
    have hpow : ((-1 : ℂ)) ^ (j + m + δ) = 1 := by
      rw [hr, ← two_mul, pow_mul]; simp
    have hw : 0 < ((z + δ) / 2).re := by
      simp only [Complex.div_re, Complex.add_re, Complex.natCast_re]
      have : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
      norm_num; positivity
    have hcast : (((j + m : ℕ) : ℂ)) = 2 * (kk j δ m : ℂ) + δ := by exact_mod_cast hk
    have harg : (z + ((j + m : ℕ) : ℂ)) / 2 = (z + δ) / 2 + (kk j δ m : ℂ) := by rw [hcast]; ring
    have hexp : -(z + ((j + m : ℕ) : ℂ)) / 2 = -((z + δ) / 2) + (-(kk j δ m : ℂ)) := by rw [hcast]; ring
    have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
    rw [harg, Gamma_add_nat_eq _ hw, hexp, Complex.cpow_add _ _ hb0, Complex.cpow_neg, Complex.cpow_neg,
      Complex.cpow_natCast,
      hpow, Complex.ofReal_inv, inv_pow]
    ring
  ·
    have hodd : ((-1 : ℂ)) ^ (j + m + δ) = -1 := by
      rw [Nat.not_even_iff_odd] at hev
      exact hev.neg_one_pow
    rw [hodd]
    ring

private theorem integrable_tateMonomialFn (m δ : ℕ) {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) :
    MeasureTheory.Integrable (tateMonomialFn m δ b z) := by
  have hIoi : IntegrableOn (tateMonomialFn m δ b z) (Ioi 0) :=
    (integrableOn_evenProfile_Ioi m hb hz).congr_fun
      (fun ρ hρ => (tateMonomialFn_of_pos m δ b z hρ).symm) measurableSet_Ioi
  have hneg : IntegrableOn (fun ρ : ℝ => evenProfile m b z (-ρ)) (Iio 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    have e : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simp_rw [Function.comp_def, neg_neg, neg_preimage, neg_Iio, neg_zero]
    exact integrableOn_evenProfile_Ioi m hb hz
  have hIio : IntegrableOn (tateMonomialFn m δ b z) (Iio 0) :=
    IntegrableOn.congr_fun (hneg.const_mul ((-1 : ℂ) ^ (m + δ)))
      (fun ρ hρ => (tateMonomialFn_of_neg m δ b z hρ).symm) measurableSet_Iio
  have hIic : IntegrableOn (tateMonomialFn m δ b z) (Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio (enorm_ne_top)).mpr hIio
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

private theorem norm_tateMonomialFn (m δ : ℕ) (b : ℝ) (z : ℂ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ‖tateMonomialFn m δ b z ρ‖ = |ρ| ^ m * (Real.exp (-(b * ρ ^ 2)) * |ρ| ^ (z.re - 1)) := by
  have habs : 0 < |ρ| := abs_pos.mpr hρ
  have hsign : ‖(Real.sign ρ : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases lt_or_gt_of_ne hρ with h | h
    · rw [Real.sign_of_neg h]; simp
    · rw [Real.sign_of_pos h]; simp
  unfold tateMonomialFn
  rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_pow, hsign, one_pow, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos habs, Complex.sub_re, Complex.one_re]
  ring

private noncomputable def tateLinFn (j δ : ℕ) (b : ℝ) (β z : ℂ) (ρ : ℝ) : ℂ :=
  (ρ : ℂ) ^ j * (Real.exp (-(b * ρ ^ 2)) : ℂ) * Complex.exp (-(β * ρ)) * (Real.sign ρ : ℂ) ^ δ *
    ((|ρ| : ℝ) : ℂ) ^ (z - 1)

private theorem tateLinFn_eq_tsum (j δ : ℕ) (b : ℝ) (β z : ℂ) (ρ : ℝ) :
    tateLinFn j δ b β z ρ = ∑' m : ℕ, (-β) ^ m / (m ! : ℂ) * tateMonomialFn (j + m) δ b z ρ := by
  have hexp : Complex.exp (-(β * ρ)) = ∑' m : ℕ, (-(β * ρ)) ^ m / (m ! : ℂ) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  calc tateLinFn j δ b β z ρ
      = ((ρ : ℂ) ^ j * (Real.exp (-(b * ρ ^ 2)) : ℂ) * (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)) *
          Complex.exp (-(β * ρ)) := by unfold tateLinFn; ring
    _ = ((ρ : ℂ) ^ j * (Real.exp (-(b * ρ ^ 2)) : ℂ) * (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)) *
          ∑' m : ℕ, (-(β * ρ)) ^ m / (m ! : ℂ) := by rw [hexp]
    _ = ∑' m : ℕ, ((ρ : ℂ) ^ j * (Real.exp (-(b * ρ ^ 2)) : ℂ) * (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)) *
          ((-(β * ρ)) ^ m / (m ! : ℂ)) := tsum_mul_left.symm
    _ = ∑' m : ℕ, (-β) ^ m / (m ! : ℂ) * tateMonomialFn (j + m) δ b z ρ := by
        congr 1; funext m
        unfold tateMonomialFn
        rw [pow_add, show -(β * (ρ : ℂ)) = (-β) * ρ by ring, mul_pow]
        ring

private theorem integrable_majorantFn (j : ℕ) {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) (β : ℂ) :
    MeasureTheory.Integrable
      (fun ρ : ℝ => Real.exp (‖β‖ * |ρ|) * (|ρ| ^ j * (Real.exp (-(b * ρ ^ 2)) * |ρ| ^ (z.re - 1)))) := by

  have hb2 : 0 < b / 2 := half_pos hb
  have hint := (integrable_tateMonomialFn j 0 hb2 hz).norm
  refine (hint.const_mul (Real.exp (‖β‖ ^ 2 / (2 * b)))).mono' ?_ ?_
  ·
    refine Measurable.aestronglyMeasurable ?_
    refine (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_abs)).mul ?_
    refine (measurable_abs.pow_const j).mul ?_
    refine (Real.continuous_exp.measurable.comp ((measurable_const.mul (measurable_id.pow_const 2)).neg)).mul ?_
    exact measurable_abs.pow_const (z.re - 1)
  · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ρ hρ
    rw [norm_tateMonomialFn j 0 (b / 2) z hρ, Real.norm_eq_abs]
    have h0 : 0 ≤ |ρ| ^ j * (Real.exp (-(b * ρ ^ 2)) * |ρ| ^ (z.re - 1)) := by positivity
    rw [abs_of_nonneg (by positivity)]

    have hkey : Real.exp (‖β‖ * |ρ|) * Real.exp (-(b * ρ ^ 2)) ≤
        Real.exp (‖β‖ ^ 2 / (2 * b)) * Real.exp (-(b / 2 * ρ ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have hsq : 0 ≤ (‖β‖ - b * |ρ|) ^ 2 := sq_nonneg _
      have habs2 : |ρ| ^ 2 = ρ ^ 2 := sq_abs ρ
      have hdiv : ‖β‖ ^ 2 / (2 * b) = ‖β‖ ^ 2 * (1 / (2 * b)) := by ring
      rw [hdiv]
      have h2b : 0 < 2 * b := by positivity

      have : ‖β‖ * |ρ| ≤ ‖β‖ ^ 2 * (1 / (2 * b)) + b / 2 * |ρ| ^ 2 := by
        rw [← sub_nonneg]
        have : ‖β‖ ^ 2 * (1 / (2 * b)) + b / 2 * |ρ| ^ 2 - ‖β‖ * |ρ| = (‖β‖ - b * |ρ|) ^ 2 / (2 * b) := by
          field_simp; ring
        rw [this]; positivity
      rw [habs2] at this
      linarith
    calc Real.exp (‖β‖ * |ρ|) * (|ρ| ^ j * (Real.exp (-(b * ρ ^ 2)) * |ρ| ^ (z.re - 1)))
        = (Real.exp (‖β‖ * |ρ|) * Real.exp (-(b * ρ ^ 2))) * (|ρ| ^ j * |ρ| ^ (z.re - 1)) := by ring
      _ ≤ (Real.exp (‖β‖ ^ 2 / (2 * b)) * Real.exp (-(b / 2 * ρ ^ 2))) * (|ρ| ^ j * |ρ| ^ (z.re - 1)) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = Real.exp (‖β‖ ^ 2 / (2 * b)) * (|ρ| ^ j * (Real.exp (-(b / 2 * ρ ^ 2)) * |ρ| ^ (z.re - 1))) := by ring

private theorem tsum_lintegral_ne_top (j δ : ℕ) {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) (β : ℂ) :
    ∑' m : ℕ, ∫⁻ ρ : ℝ, ‖(-β) ^ m / (m ! : ℂ) * tateMonomialFn (j + m) δ b z ρ‖ₑ ≠ ⊤ := by
  rw [← lintegral_tsum (fun m => ((measurable_tateMonomialFn (j + m) δ b z).const_mul _).enorm.aemeasurable)]
  refine ne_top_of_le_ne_top (integrable_majorantFn j hb hz β).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ρ hρ

  have hterm : ∀ m : ℕ, ‖(-β) ^ m / (m ! : ℂ) * tateMonomialFn (j + m) δ b z ρ‖ =
      (‖β‖ * |ρ|) ^ m / (m ! : ℝ) * (|ρ| ^ j * (Real.exp (-(b * ρ ^ 2)) * |ρ| ^ (z.re - 1))) := by
    intro m
    rw [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_natCast, norm_tateMonomialFn _ _ _ _ hρ, pow_add,
      mul_pow]
    ring
  have hsum : Summable fun m : ℕ => ‖(-β) ^ m / (m ! : ℂ) * tateMonomialFn (j + m) δ b z ρ‖ := by
    simp_rw [hterm]
    exact (Real.summable_pow_div_factorial (‖β‖ * |ρ|)).mul_right _
  have htsum : ∑' m : ℕ, ‖(-β) ^ m / (m ! : ℂ) * tateMonomialFn (j + m) δ b z ρ‖ =
      Real.exp (‖β‖ * |ρ|) * (|ρ| ^ j * (Real.exp (-(b * ρ ^ 2)) * |ρ| ^ (z.re - 1))) := by
    simp_rw [hterm]
    rw [tsum_mul_right, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp_rw [← ofReal_norm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => norm_nonneg _) hsum, htsum]

private theorem integral_tateLinFn (j δ : ℕ) (hδ : δ ≤ 1) {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) (β : ℂ) :
    ∫ ρ : ℝ, tateLinFn j δ b β z ρ =
      Complex.Gamma ((z + δ) / 2) * (b : ℂ) ^ (-((z + δ) / 2)) * eMono j δ b⁻¹ β ((z + δ) / 2) := by
  simp_rw [tateLinFn_eq_tsum]
  rw [integral_tsum (fun m => ((measurable_tateMonomialFn (j + m) δ b z).const_mul _).aestronglyMeasurable)
    (tsum_lintegral_ne_top j δ hb hz β)]
  unfold eMono
  rw [← tsum_mul_left]
  congr 1; funext m
  rw [← integral_term_eq j δ hδ hb hz β m]
  simp_rw [← smul_eq_mul (a := (-β) ^ m / (m ! : ℂ))]
  rw [integral_smul]

private theorem continuous_eMono_params (j δ : ℕ) (w : ℂ) :
    Continuous (fun q : ℝ × ℂ => eMono j δ q.1 q.2 w) := by
  rw [continuous_iff_continuousAt]
  intro q₀

  have hU : IsOpen (Metric.ball q₀ 1) := Metric.isOpen_ball
  have hmem : q₀ ∈ Metric.ball q₀ 1 := Metric.mem_ball_self one_pos
  refine ContinuousOn.continuousAt ?_ (hU.mem_nhds hmem)
  unfold eMono
  refine continuousOn_tsum (fun m => ?_)
    (summable_maj (R := ‖w‖) j δ (Bi := max (|q₀.1| + 1) 1) (Be := ‖q₀.2‖ + 1) (le_max_right _ _) (by positivity))
    (fun m q hq => ?_)
  ·
    unfold eTerm
    split_ifs
    · refine Continuous.continuousOn ?_
      fun_prop
    · exact continuousOn_const
  · have h1 : |q.1| ≤ max (|q₀.1| + 1) 1 := by
      refine le_max_of_le_left ?_
      have hd : dist q q₀ < 1 := hq
      have hfst : dist q.1 q₀.1 < 1 := by rw [Prod.dist_eq] at hd; exact lt_of_le_of_lt (le_max_left _ _) hd
      rw [Real.dist_eq] at hfst
      calc |q.1| = |(q.1 - q₀.1) + q₀.1| := by ring_nf
        _ ≤ |q.1 - q₀.1| + |q₀.1| := abs_add_le _ _
        _ ≤ |q₀.1| + 1 := by linarith
    have h2 : ‖q.2‖ ≤ ‖q₀.2‖ + 1 := by
      have hd : dist q q₀ < 1 := hq
      have hsnd : dist q.2 q₀.2 < 1 := by rw [Prod.dist_eq] at hd; exact lt_of_le_of_lt (le_max_right _ _) hd
      rw [dist_eq_norm] at hsnd
      calc ‖q.2‖ = ‖(q.2 - q₀.2) + q₀.2‖ := by ring_nf
        _ ≤ ‖q.2 - q₀.2‖ + ‖q₀.2‖ := norm_add_le _ _
        _ ≤ ‖q₀.2‖ + 1 := by linarith
    exact norm_eTerm_le j δ h1 h2 m le_rfl

open Real in

private noncomputable def Efun (n δ : ℕ) (c : Fin (n + 1) → ℂ) (A : ℝ) (β : ℂ) (z : ℂ) : ℂ :=
  if 0 < A then
    (A : ℂ) ^ (-((z + δ) / 2)) * ∑ j : Fin (n + 1), c j * eMono (j : ℕ) δ (π * A)⁻¹ β ((z + δ) / 2)
  else 0

private theorem differentiable_Efun
    (n δ : ℕ) (c : Fin (n + 1) → ℂ) (A : ℝ) (β : ℂ) : Differentiable ℂ (Efun n δ c A β) := by
  unfold Efun
  split_ifs with hA
  · have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
    refine Differentiable.mul ?_ ?_
    · exact (differentiable_id.add_const _ |>.div_const _ |>.neg).const_cpow (Or.inl hA0)
    · refine Differentiable.fun_sum (fun j _ => ?_)
      exact (differentiable_eMono (j : ℕ) δ _ β).comp (differentiable_id.add_const _ |>.div_const _) |>.const_mul _
  · exact differentiable_const 0

private theorem integrand_eq_sum (n δ : ℕ) (c : Fin (n + 1) → ℂ) {A : ℝ} (β z : ℂ) (ρ : ℝ) :
    (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) * Complex.exp (-((Real.pi * A : ℝ) * ρ ^ 2 + β * ρ)) *
        (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1) =
      ∑ j : Fin (n + 1), c j * tateLinFn (j : ℕ) δ (Real.pi * A) β z ρ := by
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold tateLinFn
  rw [show -(((Real.pi * A : ℝ) : ℂ) * ρ ^ 2 + β * ρ) = (-((Real.pi * A) * ρ ^ 2) : ℝ) + (-(β * ρ)) by push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  ring

private theorem integral_cmul (a : ℂ) (f : ℝ → ℂ) : ∫ ρ : ℝ, a * f ρ = a * ∫ ρ : ℝ, f ρ := by
  simp_rw [← smul_eq_mul]
  exact MeasureTheory.integral_smul a f

private theorem integrable_tateLinFn (j δ : ℕ) {b : ℝ} (hb : 0 < b) (β : ℂ) {z : ℂ} (hz : 0 < z.re) :
    MeasureTheory.Integrable (tateLinFn j δ b β z) := by
  refine (integrable_majorantFn j hb hz β).mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    unfold tateLinFn
    refine ((((Complex.measurable_ofReal.pow_const j).mul ?_).mul ?_).mul
      ((Complex.measurable_ofReal.comp measurable_sign).pow_const δ)).mul
      ((Complex.measurable_ofReal.comp measurable_abs).pow_const (z - 1))
    · exact Complex.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (measurable_id.pow_const 2)).neg))
    · exact Complex.continuous_exp.measurable.comp ((measurable_const.mul Complex.measurable_ofReal).neg)
  · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with ρ hρ
    have hlin : tateLinFn j δ b β z ρ = Complex.exp (-(β * ρ)) * tateMonomialFn j δ b z ρ := by
      unfold tateLinFn tateMonomialFn; ring
    rw [hlin, norm_mul, norm_tateMonomialFn j δ b z hρ, Complex.norm_exp]
    have hre : (-(β * (ρ : ℂ))).re ≤ ‖β‖ * |ρ| := by
      calc (-(β * (ρ : ℂ))).re ≤ ‖-(β * (ρ : ℂ))‖ := Complex.re_le_norm _
        _ = ‖β‖ * |ρ| := by rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hexp : Real.exp (-(β * (ρ : ℂ))).re ≤ Real.exp (‖β‖ * |ρ|) := Real.exp_le_exp.mpr hre
    exact mul_le_mul_of_nonneg_right hexp (by positivity)

private theorem integral_eq_Gammaℝ_mul_Efun (n δ : ℕ) (hδ : δ ≤ 1) (c : Fin (n + 1) → ℂ) {A : ℝ} (hA : 0 < A) (β : ℂ)
    {z : ℂ} (hz : 0 < z.re) :
    ∫ ρ : ℝ, (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) * Complex.exp (-((Real.pi * A : ℝ) * ρ ^ 2 + β * ρ)) *
        (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1) =
      Complex.Gammaℝ (z + δ) * Efun n δ c A β z := by
  have hb : 0 < Real.pi * A := by positivity
  simp_rw [integrand_eq_sum n δ c β z]
  rw [MeasureTheory.integral_finsetSum _
    (fun (j : Fin (n + 1)) _ => (integrable_tateLinFn (j : ℕ) δ hb β hz).const_mul (c j))]
  simp_rw [integral_cmul]
  rw [Finset.sum_congr rfl (fun j _ => by rw [integral_tateLinFn (j : ℕ) δ hδ hb hz β])]
  unfold Efun
  rw [if_pos hA, Complex.Gammaℝ_def, neg_div]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast
  rw [Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hA.le]
  ring

private theorem continuousOn_Efun (n δ : ℕ) (z : ℂ) :
    ContinuousOn (fun p : (Fin (n + 1) → ℂ) × ℝ × ℝ => Efun n δ p.1 p.2.1 (2 * Real.pi * (p.2.2 : ℂ)) z)
      {p : (Fin (n + 1) → ℂ) × ℝ × ℝ | 0 < p.2.1} := by
  refine ContinuousOn.congr (f := fun q : (Fin (n + 1) → ℂ) × ℝ × ℝ => (q.2.1 : ℂ) ^ (-((z + δ) / 2)) *
      ∑ j : Fin (n + 1), q.1 j * eMono (j : ℕ) δ (Real.pi * q.2.1)⁻¹ (2 * Real.pi * (q.2.2 : ℂ)) ((z + δ) / 2)) ?_
    (fun q hq => by unfold Efun; rw [if_pos (show 0 < q.2.1 from hq)])
  refine ContinuousOn.mul ?_ ?_
  · intro q hq
    apply ContinuousAt.continuousWithinAt
    have hq' : 0 < q.2.1 := hq
    exact (Complex.continuousAt_ofReal_cpow_const q.2.1 _ (Or.inr hq'.ne')).comp
      (f := fun r : (Fin (n + 1) → ℂ) × ℝ × ℝ => r.2.1) (continuous_fst.comp continuous_snd).continuousAt
  · refine continuousOn_finsetSum _ (fun j _ => ?_)
    refine ContinuousOn.mul ((continuous_apply j).comp continuous_fst).continuousOn ?_
    intro q hq
    apply ContinuousAt.continuousWithinAt
    have hq' : 0 < q.2.1 := hq
    have hpair : ContinuousAt (fun r : (Fin (n + 1) → ℂ) × ℝ × ℝ =>
        ((Real.pi * r.2.1)⁻¹, 2 * Real.pi * (r.2.2 : ℂ))) q := by
      refine ContinuousAt.prodMk ?_ ?_
      · exact (continuous_const.mul (continuous_fst.comp continuous_snd)).continuousAt.inv₀
          (by show Real.pi * q.2.1 ≠ 0; exact (mul_pos Real.pi_pos hq').ne')
      · exact (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_snd))).continuousAt
    exact ((continuous_eMono_params (j : ℕ) δ ((z + δ) / 2)).continuousAt).comp
      (f := fun r : (Fin (n + 1) → ℂ) × ℝ × ℝ => ((Real.pi * r.2.1)⁻¹, 2 * Real.pi * (r.2.2 : ℂ))) hpair

private theorem integrand_eq (n δ : ℕ) (c : Fin (n + 1) → ℂ) (A B : ℝ) (z : ℂ) (ρ : ℝ) :
    (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) * (Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ) *
        (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1) =
      (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) *
        Complex.exp (-((Real.pi * A : ℝ) * ρ ^ 2 + (2 * Real.pi * (B : ℂ)) * ρ)) *
        (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1) := by
  rw [Complex.ofReal_exp]
  congr 3
  push_cast
  ring

open Polynomial in

private noncomputable def prof (p : ℂ[X]) (b : ℝ) (β : ℂ) (ρ : ℝ) : ℂ :=
  p.eval (ρ : ℂ) * Complex.exp (-((b : ℂ) * ρ ^ 2 + β * ρ))

open Polynomial in

private noncomputable def shiftPoly (p : ℂ[X]) (b : ℝ) (β : ℂ) : ℂ[X] :=
  derivative p - (C (2 * (b : ℂ)) * X + C β) * p

open Polynomial in
private theorem hasDerivAt_prof (p : ℂ[X]) (b : ℝ) (β : ℂ) (ρ : ℝ) :
    HasDerivAt (prof p b β) (prof (shiftPoly p b β) b β ρ) ρ := by
  have h1 : HasDerivAt (fun r : ℝ => p.eval (r : ℂ)) ((derivative p).eval (ρ : ℂ)) ρ :=
    (Polynomial.hasDerivAt p (ρ : ℂ)).comp_ofReal
  have hr : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 ρ := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun r : ℝ => -((b : ℂ) * (r : ℂ) ^ 2 + β * r)) (-((b : ℂ) * (2 * ρ) + β)) ρ := by
    have := ((hr.pow 2).const_mul (b : ℂ)).add (hr.const_mul β)
    convert this.neg using 1 <;> try rfl
    push_cast
    ring
  have h3 := h2.cexp
  have h4 := h1.mul h3
  refine h4.congr_deriv ?_
  unfold prof shiftPoly
  simp only [eval_sub, eval_mul, eval_add, eval_C, eval_X]
  ring

private noncomputable def wgt (δ : ℕ) (z : ℂ) (ρ : ℝ) : ℂ := (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1)

private theorem prof_mul_wgt (p : Polynomial ℂ) (b : ℝ) (β z : ℂ) (δ : ℕ) (ρ : ℝ) :
    prof p b β ρ * wgt δ z ρ =
      p.eval (ρ : ℂ) * Complex.exp (-((b : ℂ) * ρ ^ 2 + β * ρ)) * (Real.sign ρ : ℂ) ^ δ *
        ((|ρ| : ℝ) : ℂ) ^ (z - 1) := by
  unfold prof wgt; ring

private theorem wgt_eventuallyEq {ρ : ℝ} (hρ : ρ ≠ 0) (δ : ℕ) (z : ℂ) :
    wgt δ z =ᶠ[nhds ρ] fun r : ℝ => (Real.sign ρ : ℂ) ^ δ * ((|r| : ℝ) : ℂ) ^ (z - 1) := by
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · filter_upwards [Iio_mem_nhds hneg] with r hr
    unfold wgt
    rw [Real.sign_of_neg (Set.mem_Iio.mp hr), Real.sign_of_neg hneg]
  · filter_upwards [Ioi_mem_nhds hpos] with r hr
    unfold wgt
    rw [Real.sign_of_pos (Set.mem_Ioi.mp hr), Real.sign_of_pos hpos]

private theorem ofReal_abs_eq_sign_mul
    {ρ : ℝ} (hρ : ρ ≠ 0) : ((|ρ| : ℝ) : ℂ) = ((SignType.sign ρ : ℝ) : ℂ) * (ρ : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  rcases lt_or_gt_of_ne hρ with hn | hp
  · simp [abs_of_neg hn, sign_neg hn]
  · simp [abs_of_pos hp, sign_pos hp]

private theorem hasDerivAt_wgt (δ : ℕ) (z : ℂ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    HasDerivAt (wgt δ z) ((z - 1) * wgt δ z ρ / ρ) ρ := by
  have hpos : (0 : ℝ) < |ρ| := abs_pos.mpr hρ
  have hslit : ((|ρ| : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hpos
  have hin : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (z - 1)) ((z - 1) * ((|ρ| : ℝ) : ℂ) ^ (z - 1 - 1)) |ρ| :=
    (Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt.comp_ofReal
  have hcomp : HasDerivAt (fun r : ℝ => ((|r| : ℝ) : ℂ) ^ (z - 1))
      ((SignType.sign ρ : ℝ) • ((z - 1) * ((|ρ| : ℝ) : ℂ) ^ (z - 1 - 1))) ρ :=
    HasDerivAt.scomp (x := ρ) hin (hasDerivAt_abs hρ)
  have h2 : HasDerivAt (wgt δ z)
      ((Real.sign ρ : ℂ) ^ δ * ((SignType.sign ρ : ℝ) • ((z - 1) * ((|ρ| : ℝ) : ℂ) ^ (z - 1 - 1)))) ρ :=
    (hcomp.const_mul ((Real.sign ρ : ℂ) ^ δ)).congr_of_eventuallyEq (wgt_eventuallyEq hρ δ z)
  convert h2 using 1
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ
  have hne : ((|ρ| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have hpow : ((|ρ| : ℝ) : ℂ) ^ (z - 1) = ((|ρ| : ℝ) : ℂ) ^ (z - 1 - 1) * ((|ρ| : ℝ) : ℂ) := by
    conv_lhs => rw [← sub_add_cancel (z - 1) 1]
    rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
  rw [Complex.real_smul]
  unfold wgt
  rw [hpow, div_eq_iff hρc, ofReal_abs_eq_sign_mul hρ]
  ring

private theorem ofReal_mul_wgt (δ : ℕ) (hδ : δ ≤ 1) (z : ℂ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    (ρ : ℂ) * wgt δ z ρ = wgt (1 - δ) (z + 1) ρ := by
  have hne : ((|ρ| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_pos.mpr hρ).ne'
  have hsplit : ((|ρ| : ℝ) : ℂ) ^ (z + 1 - 1) = ((|ρ| : ℝ) : ℂ) ^ (z - 1) * ((|ρ| : ℝ) : ℂ) := by
    rw [show z + 1 - 1 = (z - 1) + 1 by ring, Complex.cpow_add _ _ hne, Complex.cpow_one]
  unfold wgt
  rw [hsplit]

  have hρeq : (ρ : ℂ) = (Real.sign ρ : ℂ) * ((|ρ| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rcases lt_or_gt_of_ne hρ with hn | hp
    · rw [Real.sign_of_neg hn, abs_of_neg hn]; ring
    · rw [Real.sign_of_pos hp, abs_of_pos hp]; ring
  have hsq : (Real.sign ρ : ℂ) * (Real.sign ρ : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    rcases Real.sign_apply_eq_of_ne_zero ρ hρ with hs | hs <;> rw [hs] <;> norm_num
  rw [hρeq]
  interval_cases δ
  · simp only [pow_zero, Nat.sub_zero, pow_one]; ring
  · simp only [pow_one, Nat.sub_self, pow_zero]
    linear_combination (((|ρ| : ℝ) : ℂ) ^ (z - 1) * ((|ρ| : ℝ) : ℂ)) * hsq

open Polynomial in

private noncomputable def Epoly (n δ : ℕ) (p : ℂ[X]) (A : ℝ) (β : ℂ) (z : ℂ) : ℂ :=
  Efun n δ (fun j : Fin (n + 1) => p.coeff j) A β z

open Polynomial in
private theorem eval_eq_fin_sum {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) (x : ℂ) :
    p.eval x = ∑ j : Fin (n + 1), p.coeff j * x ^ (j : ℕ) := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp), Fin.sum_univ_eq_sum_range (fun i => p.coeff i * x ^ i)]

open Polynomial in

private theorem integral_prof_mul_wgt
    {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) (δ : ℕ) (hδ : δ ≤ 1) {A : ℝ} (hA : 0 < A)
    (β : ℂ) {z : ℂ} (hz : 0 < z.re) :
    ∫ ρ : ℝ, prof p (Real.pi * A) β ρ * wgt δ z ρ = Complex.Gammaℝ (z + δ) * Epoly n δ p A β z := by
  unfold Epoly
  rw [← integral_eq_Gammaℝ_mul_Efun n δ hδ _ hA β hz]
  congr 1; funext ρ
  rw [prof_mul_wgt, eval_eq_fin_sum hp]

open Polynomial in
private theorem integrable_prof_mul_wgt {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) (δ : ℕ) {b : ℝ} (hb : 0 < b) (β : ℂ)
    {z : ℂ} (hz : 0 < z.re) : MeasureTheory.Integrable (fun ρ : ℝ => prof p b β ρ * wgt δ z ρ) := by
  have : (fun ρ : ℝ => prof p b β ρ * wgt δ z ρ) =
      fun ρ => ∑ j : Fin (n + 1), p.coeff j * tateLinFn (j : ℕ) δ b β z ρ := by
    funext ρ
    rw [prof_mul_wgt, eval_eq_fin_sum hp, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold tateLinFn
    rw [show -((b : ℂ) * (ρ : ℂ) ^ 2 + β * ρ) = (-(b * ρ ^ 2) : ℝ) + (-(β * ρ)) by push_cast; ring, Complex.exp_add,
      ← Complex.ofReal_exp]
    ring
  rw [this]
  exact MeasureTheory.integrable_finsetSum _ (fun j _ => (integrable_tateLinFn (j : ℕ) δ hb β hz).const_mul _)

open Polynomial in
private theorem natDegree_shiftPoly_le {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) (b : ℝ) (β : ℂ) :
    (shiftPoly p b β).natDegree ≤ n + 1 := by
  unfold shiftPoly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_derivative_le p).trans (by omega)
  · refine natDegree_mul_le.trans ?_
    have h1 : (C (2 * (b : ℂ)) * X + C β).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
    omega

open Polynomial in

private theorem shift_identity_of_re_pos
    {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) (δ : ℕ) (hδ : δ ≤ 1) {A : ℝ} (hA : 0 < A)
    (β : ℂ) {z : ℂ} (hz : 0 < z.re) :
    z * (Complex.Gammaℝ (z + δ) * Epoly n δ p A β z) =
      -(Complex.Gammaℝ (z + 1 + ((1 - δ : ℕ) : ℂ)) *
        Epoly (n + 1) (1 - δ) (shiftPoly p (Real.pi * A) β) A β (z + 1)) := by
  have hb : 0 < Real.pi * A := by positivity
  have hz1 : 0 < (z + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  set q := shiftPoly p (Real.pi * A) β with hq

  have hf₁ : (fun ρ : ℝ => ((ρ : ℂ) * prof q (Real.pi * A) β ρ) * wgt δ z ρ) =ᵐ[MeasureTheory.volume]
      fun ρ : ℝ => prof q (Real.pi * A) β ρ * wgt (1 - δ) (z + 1) ρ := by
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with ρ hρ
    rw [← ofReal_mul_wgt δ hδ z hρ]; ring
  have hint₁ : MeasureTheory.Integrable (fun ρ : ℝ => ((ρ : ℂ) * prof q (Real.pi * A) β ρ) * wgt δ z ρ) :=
    (integrable_prof_mul_wgt (natDegree_shiftPoly_le hp _ _) (1 - δ) hb β hz1).congr hf₁.symm
  have key := MellinByParts.whole (f := prof p (Real.pi * A) β) (f₁ := fun ρ : ℝ => (ρ : ℂ) * prof q (Real.pi * A) β ρ)
    (w := wgt δ z) (c := z - 1)
    (fun ρ hρ => by
      have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ
      have := hasDerivAt_prof p (Real.pi * A) β ρ
      rw [← hq] at this
      convert this using 1
      field_simp)
    (fun ρ hρ => hasDerivAt_wgt δ z hρ)
    (integrable_prof_mul_wgt hp δ hb β hz) hint₁
  rw [sub_add_cancel, integral_prof_mul_wgt hp δ hδ hA β hz] at key
  rw [key, MeasureTheory.integral_congr_ae hf₁,
    integral_prof_mul_wgt (natDegree_shiftPoly_le hp _ _) (1 - δ) (by omega) hA β hz1]

open Polynomial in
private theorem differentiable_Epoly (n δ : ℕ) (p : ℂ[X]) (A : ℝ) (β : ℂ) : Differentiable ℂ (Epoly n δ p A β) :=
  differentiable_Efun n δ _ A β

private theorem rePos_mem_nhds_one : {z : ℂ | 0 < z.re} ∈ nhds (1 : ℂ) :=
  (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)

open Polynomial in

private theorem shift_one {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) {A : ℝ} (hA : 0 < A) (β : ℂ) (z : ℂ) :
    z * Epoly n 1 p A β z = -Epoly (n + 1) 0 (shiftPoly p (Real.pi * A) β) A β (z + 1) := by
  have hf : Differentiable ℂ (fun z : ℂ => z * Epoly n 1 p A β z) :=
    differentiable_id.mul (differentiable_Epoly n 1 p A β)
  have hg : Differentiable ℂ (fun z : ℂ => -Epoly (n + 1) 0 (shiftPoly p (Real.pi * A) β) A β (z + 1)) :=
    ((differentiable_Epoly _ _ _ A β).comp (differentiable_id.add_const 1)).neg
  have heq : (fun z : ℂ => z * Epoly n 1 p A β z) =ᶠ[nhds (1 : ℂ)]
      fun z : ℂ => -Epoly (n + 1) 0 (shiftPoly p (Real.pi * A) β) A β (z + 1) := by
    filter_upwards [rePos_mem_nhds_one] with z hz
    have key := shift_identity_of_re_pos hp 1 le_rfl hA β hz
    simp only [Nat.sub_self, Nat.cast_zero, add_zero, Nat.cast_one] at key
    have hΓ : Complex.Gammaℝ (z + 1) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.one_re]; linarith)
    apply mul_left_cancel₀ hΓ
    linear_combination key
  exact congrFun (AnalyticOnNhd.eq_of_eventuallyEq (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg) heq) z

open Polynomial in

private theorem shift_zero {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) {A : ℝ} (hA : 0 < A) (β : ℂ) (z : ℂ) :
    2 * (Real.pi : ℂ) * Epoly n 0 p A β z = -Epoly (n + 1) 1 (shiftPoly p (Real.pi * A) β) A β (z + 1) := by
  have hf : Differentiable ℂ (fun z : ℂ => 2 * (Real.pi : ℂ) * Epoly n 0 p A β z) :=
    (differentiable_Epoly n 0 p A β).const_mul _
  have hg : Differentiable ℂ (fun z : ℂ => -Epoly (n + 1) 1 (shiftPoly p (Real.pi * A) β) A β (z + 1)) :=
    ((differentiable_Epoly _ _ _ A β).comp (differentiable_id.add_const 1)).neg
  have heq : (fun z : ℂ => 2 * (Real.pi : ℂ) * Epoly n 0 p A β z) =ᶠ[nhds (1 : ℂ)]
      fun z : ℂ => -Epoly (n + 1) 1 (shiftPoly p (Real.pi * A) β) A β (z + 1) := by
    filter_upwards [rePos_mem_nhds_one] with z hz
    have key := shift_identity_of_re_pos hp 0 (Nat.zero_le 1) hA β hz
    simp only [Nat.sub_zero, Nat.cast_zero, add_zero, Nat.cast_one] at key
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz
    have hΓ : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hz
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [show z + 1 + 1 = z + 2 by ring, Complex.Gammaℝ_add_two hz0] at key
    field_simp at key
    linear_combination key
  exact congrFun (AnalyticOnNhd.eq_of_eventuallyEq (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg) heq) z

private theorem isCompact_band (a b : ℝ) :
    IsCompact ((fun w : ℂ => (w.re, w.im)) ⁻¹' (Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1)) :=
  (Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage).mpr (isCompact_Icc.prod isCompact_Icc)

private theorem Gamma_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) : Complex.Gamma w ≠ 0 := by
  refine Complex.Gamma_ne_zero (fun m hm => ?_)
  have := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at this
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

private theorem continuousAt_Gamma_of_re_pos {w : ℂ} (hw : 0 < w.re) : ContinuousAt Complex.Gamma w := by
  refine (Complex.differentiableAt_Gamma w (fun m hm => ?_)).continuousAt
  have := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at this
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

private theorem exists_inv_norm_Gamma_le (a b : ℝ) (ha : 0 < a) :
    ∃ C M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖Complex.Gamma w‖⁻¹ ≤ C * Real.exp (M * |w.im|) := by
  by_cases hab : a ≤ b
  swap
  · exact ⟨0, 0, le_rfl, fun w h1 h2 => absurd (h1.trans h2) (not_le.mpr (not_le.mp hab))⟩
  obtain ⟨A, N, hAN⟩ :=
    Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im a b

  set K : Set ℂ := (fun w : ℂ => (w.re, w.im)) ⁻¹' (Set.Icc a b ×ˢ Set.Icc (-1 : ℝ) 1) with hK
  have hKc : IsCompact K := isCompact_band a b
  have hKne : K.Nonempty := ⟨(a : ℂ), by simp [hK, hab]⟩
  have hcont : ContinuousOn (fun w : ℂ => ‖Complex.Gamma w‖) K := by
    intro w hw
    have hwre : a ≤ w.re := (Set.mem_prod.mp hw).1.1
    exact (continuousAt_Gamma_of_re_pos (ha.trans_le hwre)).norm.continuousWithinAt
  obtain ⟨w₀, hw₀, hmin⟩ := hKc.exists_isMinOn hKne hcont
  have hc₀ : 0 < ‖Complex.Gamma w₀‖ :=
    norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (ha.trans_le (Set.mem_prod.mp hw₀).1.1))
  refine ⟨max A ‖Complex.Gamma w₀‖⁻¹, N + Real.pi / 2, by positivity, fun w hwa hwb => ?_⟩
  have hΓw : 0 < ‖Complex.Gamma w‖ := norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (ha.trans_le hwa))
  have hexp1 : 1 ≤ Real.exp ((N + Real.pi / 2) * |w.im|) := Real.one_le_exp (by positivity)
  by_cases him : 1 ≤ |w.im|
  ·
    have hlow := (hAN w hwa hwb him).2
    have hA0 : 0 < A := by
      by_contra hA
      push Not at hA
      have : A * (1 + |w.im|) ^ N * ‖Complex.Gamma w‖ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hA (by positivity)) hΓw.le
      linarith [Real.exp_pos (-(Real.pi / 2) * |w.im|)]
    have hpow : (1 + |w.im|) ^ N ≤ Real.exp ((N : ℝ) * |w.im|) := by
      rw [Real.exp_nat_mul]
      refine pow_le_pow_left₀ (by positivity) ?_ N
      linarith [Real.add_one_le_exp |w.im|]
    have h1 : ‖Complex.Gamma w‖⁻¹ ≤ A * (1 + |w.im|) ^ N * Real.exp (Real.pi / 2 * |w.im|) := by
      rw [inv_eq_one_div, div_le_iff₀ hΓw]
      have hprod : Real.exp (-(Real.pi / 2) * |w.im|) * Real.exp (Real.pi / 2 * |w.im|) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      calc (1 : ℝ) = Real.exp (-(Real.pi / 2) * |w.im|) * Real.exp (Real.pi / 2 * |w.im|) := hprod.symm
        _ ≤ (A * (1 + |w.im|) ^ N * ‖Complex.Gamma w‖) * Real.exp (Real.pi / 2 * |w.im|) :=
            mul_le_mul_of_nonneg_right hlow (Real.exp_pos _).le
        _ = A * (1 + |w.im|) ^ N * Real.exp (Real.pi / 2 * |w.im|) * ‖Complex.Gamma w‖ := by ring
    calc ‖Complex.Gamma w‖⁻¹ ≤ A * (1 + |w.im|) ^ N * Real.exp (Real.pi / 2 * |w.im|) := h1
      _ ≤ A * Real.exp ((N : ℝ) * |w.im|) * Real.exp (Real.pi / 2 * |w.im|) := by gcongr
      _ = A * Real.exp ((N + Real.pi / 2) * |w.im|) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ max A ‖Complex.Gamma w₀‖⁻¹ * Real.exp ((N + Real.pi / 2) * |w.im|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  ·
    push Not at him
    have hwK : w ∈ K := by
      simp only [hK, Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
      exact ⟨⟨hwa, hwb⟩, abs_le.mp him.le⟩
    have hle : ‖Complex.Gamma w₀‖ ≤ ‖Complex.Gamma w‖ := hmin hwK
    calc ‖Complex.Gamma w‖⁻¹ ≤ ‖Complex.Gamma w₀‖⁻¹ := inv_anti₀ hc₀ hle
      _ ≤ max A ‖Complex.Gamma w₀‖⁻¹ := le_max_right _ _
      _ = max A ‖Complex.Gamma w₀‖⁻¹ * 1 := (mul_one _).symm
      _ ≤ max A ‖Complex.Gamma w₀‖⁻¹ * Real.exp ((N + Real.pi / 2) * |w.im|) :=
          mul_le_mul_of_nonneg_left hexp1 (le_max_of_le_right (inv_pos.mpr hc₀).le)

private theorem exists_inv_norm_Gammaℝ_le (a b : ℝ) (ha : 0 < a) :
    ∃ C M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Complex.Gammaℝ s‖⁻¹ ≤ C * Real.exp (M * |s.im|) := by
  obtain ⟨C, M, hM, hCM⟩ := exists_inv_norm_Gamma_le (a / 2) (b / 2) (half_pos ha)
  refine ⟨Real.pi ^ (b / 2) * C, M, hM, fun s hsa hsb => ?_⟩
  have hre : (s / 2).re = s.re / 2 := by simp
  have him : |(s / 2).im| ≤ |s.im| := by
    have : (s / 2).im = s.im / 2 := by simp
    rw [this, abs_div, abs_two]
    exact half_le_self (abs_nonneg _)
  have hΓ := hCM (s / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  have hΓ' : ‖Complex.Gamma (s / 2)‖⁻¹ ≤ C * Real.exp (M * |s.im|) :=
    hΓ.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left him hM)) ?_)
  swap
  ·
    have hpos : 0 < ‖Complex.Gamma (s / 2)‖⁻¹ :=
      inv_pos.mpr (norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (by rw [hre]; linarith)))
    by_contra hC
    push Not at hC
    have : C * Real.exp (M * |(s / 2).im|) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC.le (Real.exp_pos _).le
    linarith
  have hnorm : ‖Complex.Gammaℝ s‖ = Real.pi ^ (-s.re / 2) * ‖Complex.Gamma (s / 2)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 2
    simp
  rw [hnorm, mul_inv, ← Real.rpow_neg Real.pi_pos.le, neg_div, neg_neg]
  have hrp : Real.pi ^ (s.re / 2) ≤ Real.pi ^ (b / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  calc Real.pi ^ (s.re / 2) * ‖Complex.Gamma (s / 2)‖⁻¹ ≤ Real.pi ^ (b / 2) * (C * Real.exp (M * |s.im|)) :=
        mul_le_mul hrp hΓ' (inv_nonneg.mpr (norm_nonneg _)) (Real.rpow_nonneg Real.pi_pos.le _)
    _ = Real.pi ^ (b / 2) * C * Real.exp (M * |s.im|) := by ring

private theorem norm_wgt {δ : ℕ} {z : ℂ} {ρ : ℝ} (hρ : ρ ≠ 0) : ‖wgt δ z ρ‖ = |ρ| ^ (z.re - 1) := by
  have habs : 0 < |ρ| := abs_pos.mpr hρ
  have hsign : ‖(Real.sign ρ : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases Real.sign_apply_eq_of_ne_zero ρ hρ with hs | hs <;> rw [hs] <;> norm_num
  unfold wgt
  rw [norm_mul, norm_pow, hsign, one_pow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos habs, Complex.sub_re,
    Complex.one_re]

open Polynomial in
private theorem norm_eval_le {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) (ρ : ℝ) :
    ‖p.eval (ρ : ℂ)‖ ≤ ∑ j : Fin (n + 1), ‖p.coeff j‖ * |ρ| ^ (j : ℕ) := by
  rw [eval_eq_fin_sum hp]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

private theorem norm_cexp_eq {A : ℝ} (hA : 0 < A) (B ρ : ℝ) :
    ‖Complex.exp (-((Real.pi * A : ℝ) * (ρ : ℂ) ^ 2 + (2 * Real.pi * (B : ℂ)) * ρ))‖ =
      Real.exp (Real.pi * B ^ 2 / A) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  have : (-((Real.pi * A : ℝ) * (ρ : ℂ) ^ 2 + (2 * Real.pi * (B : ℂ)) * ρ)) =
      ((-(Real.pi * A * ρ ^ 2 + 2 * Real.pi * B * ρ) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]
  field_simp
  ring

private theorem pow_mul_rpow_mul_exp_le {n : ℕ} (j : Fin (n + 1)) {σ σ₂ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ₂ : σ ≤ σ₂) {A : ℝ}
    (hA : 0 < A) (c : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    |ρ| ^ (j : ℕ) * |ρ| ^ (σ - 1) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) ≤
      Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (-(1 / 2 : ℝ))) +
        |ρ| ^ (n + ⌈σ₂⌉₊) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) := by
  have habs : 0 < |ρ| := abs_pos.mpr hρ
  have hE : Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := mul_nonneg (mul_nonneg Real.pi_pos.le hA.le) (sq_nonneg (ρ + c)); linarith)
  have hE0 : 0 ≤ Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) := (Real.exp_pos _).le
  rcases le_or_gt |ρ| 1 with h1 | h1
  ·
    have hj : |ρ| ^ (j : ℕ) ≤ 1 := pow_le_one₀ habs.le h1
    have hr : |ρ| ^ (σ - 1) ≤ |ρ| ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge habs h1 (by linarith)
    have hg : 1 ≤ Real.exp 1 * Real.exp (-(1 * ρ ^ 2)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have : ρ ^ 2 ≤ 1 := by
        have := sq_abs ρ
        nlinarith [habs]
      linarith
    have hpos2 : 0 ≤ |ρ| ^ (n + ⌈σ₂⌉₊) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) := by positivity
    calc |ρ| ^ (j : ℕ) * |ρ| ^ (σ - 1) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2))
        ≤ 1 * |ρ| ^ (-(1 / 2 : ℝ)) * 1 := by
          gcongr
      _ = |ρ| ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ (Real.exp 1 * Real.exp (-(1 * ρ ^ 2))) * |ρ| ^ (-(1 / 2 : ℝ)) :=
          le_mul_of_one_le_left (Real.rpow_nonneg habs.le _) hg
      _ = Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ _ := le_add_of_nonneg_right hpos2
  ·
    have hj : |ρ| ^ (j : ℕ) ≤ |ρ| ^ n := pow_le_pow_right₀ h1.le (Nat.lt_succ_iff.mp j.2)
    have hr : |ρ| ^ (σ - 1) ≤ |ρ| ^ (⌈σ₂⌉₊ : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1.le (by linarith [Nat.le_ceil σ₂])
    have hpos1 : 0 ≤ Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (-(1 / 2 : ℝ))) := by positivity
    calc |ρ| ^ (j : ℕ) * |ρ| ^ (σ - 1) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2))
        ≤ |ρ| ^ n * |ρ| ^ (⌈σ₂⌉₊ : ℕ) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) := by
          gcongr
      _ = |ρ| ^ (n + ⌈σ₂⌉₊) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) := by rw [pow_add]
      _ ≤ _ := le_add_of_nonneg_left hpos1

private theorem add_pow_le_two_pow_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (K : ℕ) :
    (x + y) ^ K ≤ 2 ^ K * (x ^ K + y ^ K) := by
  have h1 : x + y ≤ 2 * max x y := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : max x y ^ K ≤ x ^ K + y ^ K := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (pow_nonneg hx K)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (pow_nonneg hy K)
  calc (x + y) ^ K ≤ (2 * max x y) ^ K := pow_le_pow_left₀ (by positivity) h1 K
    _ = 2 ^ K * max x y ^ K := mul_pow _ _ _
    _ ≤ 2 ^ K * (x ^ K + y ^ K) := by gcongr

private theorem pow_mul_exp_le_gaussians (K : ℕ) {A : ℝ} (hA : 0 < A) (c ρ : ℝ) :
    |ρ| ^ K * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) ≤
      2 ^ K * (1 + |c| ^ K) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) +
        2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.exp (-(Real.pi * A / 2 * (ρ + c) ^ 2)) := by
  set u := ρ + c with hu
  have hb : 0 < Real.pi * A := by positivity
  have hρu : |ρ| ≤ |u| + |c| := by
    calc |ρ| = |u - c| := by rw [hu]; ring_nf
      _ ≤ |u| + |c| := abs_sub _ _
  have h1 : |ρ| ^ K ≤ 2 ^ K * (|u| ^ K + |c| ^ K) :=
    (pow_le_pow_left₀ (abs_nonneg ρ) hρu K).trans (add_pow_le_two_pow_mul (abs_nonneg u) (abs_nonneg c) K)

  have h2 : |u| ^ K ≤ 1 + |u| ^ (2 * K) := by
    rcases le_or_gt |u| 1 with hle | hgt
    · exact (pow_le_one₀ (abs_nonneg u) hle).trans (le_add_of_nonneg_right (by positivity))
    · exact (pow_le_pow_right₀ hgt.le (by omega)).trans (le_add_of_nonneg_left zero_le_one)
  have h3 : |u| ^ (2 * K) ≤ (K ! : ℝ) * (2 / (Real.pi * A)) ^ K * Real.exp (Real.pi * A / 2 * u ^ 2) := by
    have hx : 0 ≤ Real.pi * A / 2 * u ^ 2 := by positivity
    have hpf := Real.pow_div_factorial_le_exp (x := Real.pi * A / 2 * u ^ 2) hx K

    have hid : |u| ^ (2 * K) = (Real.pi * A / 2 * u ^ 2) ^ K * (2 / (Real.pi * A)) ^ K := by
      rw [pow_mul, sq_abs, ← mul_pow]
      congr 1
      field_simp
    rw [hid]
    have : (Real.pi * A / 2 * u ^ 2) ^ K ≤ (K ! : ℝ) * Real.exp (Real.pi * A / 2 * u ^ 2) := by
      rw [div_le_iff₀ (by positivity)] at hpf
      linarith
    calc (Real.pi * A / 2 * u ^ 2) ^ K * (2 / (Real.pi * A)) ^ K
        ≤ ((K ! : ℝ) * Real.exp (Real.pi * A / 2 * u ^ 2)) * (2 / (Real.pi * A)) ^ K :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = (K ! : ℝ) * (2 / (Real.pi * A)) ^ K * Real.exp (Real.pi * A / 2 * u ^ 2) := by ring
  have hexp : Real.exp (Real.pi * A / 2 * u ^ 2) * Real.exp (-(Real.pi * A * u ^ 2)) =
      Real.exp (-(Real.pi * A / 2 * u ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hE0 : 0 ≤ Real.exp (-(Real.pi * A * u ^ 2)) := (Real.exp_pos _).le
  calc |ρ| ^ K * Real.exp (-(Real.pi * A * u ^ 2))
      ≤ 2 ^ K * (|u| ^ K + |c| ^ K) * Real.exp (-(Real.pi * A * u ^ 2)) := mul_le_mul_of_nonneg_right h1 hE0
    _ ≤ 2 ^ K * ((1 + (K ! : ℝ) * (2 / (Real.pi * A)) ^ K * Real.exp (Real.pi * A / 2 * u ^ 2)) + |c| ^ K) *
          Real.exp (-(Real.pi * A * u ^ 2)) := by
        gcongr
        exact h2.trans (by linarith)
    _ = 2 ^ K * (1 + |c| ^ K) * Real.exp (-(Real.pi * A * u ^ 2)) +
          2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) *
            (Real.exp (Real.pi * A / 2 * u ^ 2) * Real.exp (-(Real.pi * A * u ^ 2))) := by ring
    _ = _ := by rw [hexp]

private theorem half_re_sub_one : ((1 / 2 : ℂ)).re - 1 = -(1 / 2 : ℝ) := by norm_num

private theorem integrable_sing
    : MeasureTheory.Integrable (fun ρ : ℝ => Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (-(1 / 2 : ℝ))) := by
  have h := (integrable_tateMonomialFn 0 0 (b := 1) one_pos (z := (1 / 2 : ℂ)) (by norm_num)).norm
  refine h.congr ?_
  filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with ρ hρ
  rw [norm_tateMonomialFn 0 0 1 _ hρ, half_re_sub_one, pow_zero, one_mul]

private theorem integral_exp_neg_mul_sq_add (b c : ℝ) :
    ∫ ρ : ℝ, Real.exp (-(b * (ρ + c) ^ 2)) = Real.sqrt (Real.pi / b) := by
  have h := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume)
    (fun t : ℝ => Real.exp (-(b * t ^ 2))) c
  rw [h, ← integral_gaussian b]
  congr 1; funext t; ring_nf

private theorem integrable_exp_neg_mul_sq_add {b : ℝ} (hb : 0 < b) (c : ℝ) :
    MeasureTheory.Integrable (fun ρ : ℝ => Real.exp (-(b * (ρ + c) ^ 2))) := by
  have h := (integrable_exp_neg_mul_sq hb).comp_add_right c
  refine h.congr (Filter.Eventually.of_forall (fun ρ => ?_))
  beta_reduce
  ring_nf

private noncomputable def majG (K : ℕ) (A c : ℝ) (ρ : ℝ) : ℝ :=
  Real.exp 1 * (Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (-(1 / 2 : ℝ))) +
    2 ^ K * (1 + |c| ^ K) * Real.exp (-(Real.pi * A * (ρ + c) ^ 2)) +
      2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.exp (-(Real.pi * A / 2 * (ρ + c) ^ 2))

private theorem integrable_majG (K : ℕ) {A : ℝ} (hA : 0 < A) (c : ℝ) : MeasureTheory.Integrable (majG K A c) := by
  unfold majG
  refine ((integrable_sing.const_mul _).add ((integrable_exp_neg_mul_sq_add (by positivity) c).const_mul _)).add
    ((integrable_exp_neg_mul_sq_add (by positivity) c).const_mul _)

private theorem integral_majG (K : ℕ) {A : ℝ} (hA : 0 < A) (c : ℝ) :
    ∫ ρ : ℝ, majG K A c ρ =
      Real.exp 1 * (∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (-(1 / 2 : ℝ))) +
        2 ^ K * (1 + |c| ^ K) * Real.sqrt (Real.pi / (Real.pi * A)) +
          2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.sqrt (Real.pi / (Real.pi * A / 2)) := by
  unfold majG
  rw [MeasureTheory.integral_add, MeasureTheory.integral_add, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, integral_exp_neg_mul_sq_add _ c,
    integral_exp_neg_mul_sq_add _ c]
  all_goals first
    | exact integrable_sing.const_mul _
    | exact (integrable_exp_neg_mul_sq_add (by positivity) c).const_mul _
    | exact (integrable_sing.const_mul _).add ((integrable_exp_neg_mul_sq_add (by positivity) c).const_mul _)

private theorem nonneg_majG (K : ℕ) {A : ℝ} (hA : 0 < A) (c ρ : ℝ) : 0 ≤ majG K A c ρ := by
  unfold majG; positivity

open Polynomial in

private theorem norm_prof_mul_wgt_le
    {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) (δ : ℕ) {σ₂ : ℝ} {A : ℝ} (hA : 0 < A) (B : ℝ)
    {z : ℂ} (hz1 : 1 / 2 ≤ z.re) (hz2 : z.re ≤ σ₂) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ‖prof p (Real.pi * A) (2 * Real.pi * (B : ℂ)) ρ * wgt δ z ρ‖ ≤
      Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖p.coeff j‖) * majG (n + ⌈σ₂⌉₊) A (B / A) ρ := by
  have hG := nonneg_majG (n + ⌈σ₂⌉₊) hA (B / A) ρ
  unfold prof
  rw [norm_mul, norm_mul, norm_wgt hρ]
  have hcexp : ‖Complex.exp (-(((Real.pi * A : ℝ) : ℂ) * (ρ : ℂ) ^ 2 + 2 * Real.pi * (B : ℂ) * ρ))‖ =
      Real.exp (Real.pi * B ^ 2 / A) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)) := norm_cexp_eq hA B ρ
  rw [hcexp]

  have hmono : ∀ j : Fin (n + 1),
      |ρ| ^ (j : ℕ) * |ρ| ^ (z.re - 1) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)) ≤
        majG (n + ⌈σ₂⌉₊) A (B / A) ρ := by
    intro j
    refine (pow_mul_rpow_mul_exp_le j hz1 hz2 hA (B / A) hρ).trans ?_
    unfold majG
    have := pow_mul_exp_le_gaussians (n + ⌈σ₂⌉₊) hA (B / A) ρ
    linarith
  have hev := norm_eval_le hp ρ
  have hE0 : 0 ≤ Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)) := (Real.exp_pos _).le
  have hw0 : 0 ≤ |ρ| ^ (z.re - 1) := Real.rpow_nonneg (abs_nonneg ρ) _
  have hP0 : 0 < Real.exp (Real.pi * B ^ 2 / A) := Real.exp_pos _
  calc ‖p.eval (ρ : ℂ)‖ * (Real.exp (Real.pi * B ^ 2 / A) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2))) *
        |ρ| ^ (z.re - 1)
      = Real.exp (Real.pi * B ^ 2 / A) *
          (‖p.eval (ρ : ℂ)‖ * (|ρ| ^ (z.re - 1) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)))) := by ring
    _ ≤ Real.exp (Real.pi * B ^ 2 / A) *
          ((∑ j : Fin (n + 1), ‖p.coeff j‖ * |ρ| ^ (j : ℕ)) *
            (|ρ| ^ (z.re - 1) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2)))) := by
        gcongr
    _ = Real.exp (Real.pi * B ^ 2 / A) *
          ∑ j : Fin (n + 1), ‖p.coeff j‖ *
            (|ρ| ^ (j : ℕ) * |ρ| ^ (z.re - 1) * Real.exp (-(Real.pi * A * (ρ + B / A) ^ 2))) := by
        rw [Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
    _ ≤ Real.exp (Real.pi * B ^ 2 / A) * ∑ j : Fin (n + 1), ‖p.coeff j‖ * majG (n + ⌈σ₂⌉₊) A (B / A) ρ := by
        gcongr with j _
        exact hmono j
    _ = Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖p.coeff j‖) * majG (n + ⌈σ₂⌉₊) A (B / A) ρ := by
        rw [← Finset.sum_mul]; ring

open Polynomial in

private theorem integral_norm_prof_mul_wgt_le
    {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) (δ : ℕ) {σ₂ : ℝ} {A : ℝ} (hA : 0 < A)
    (B : ℝ) {z : ℂ} (hz1 : 1 / 2 ≤ z.re) (hz2 : z.re ≤ σ₂) :
    ∫ ρ : ℝ, ‖prof p (Real.pi * A) (2 * Real.pi * (B : ℂ)) ρ * wgt δ z ρ‖ ≤
      Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖p.coeff j‖) * ∫ ρ : ℝ, majG (n + ⌈σ₂⌉₊) A (B / A) ρ := by
  have hb : 0 < Real.pi * A := by positivity
  have hz : 0 < z.re := by linarith
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_ae (integrable_prof_mul_wgt hp δ hb _ hz).norm
    ((integrable_majG _ hA _).const_mul _) ?_
  filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with ρ hρ
  exact norm_prof_mul_wgt_le hp δ hA B hz1 hz2 hρ

private theorem one_le_maxA {A : ℝ} (hA : 0 < A) : 1 ≤ max A A⁻¹ := by
  rcases le_or_gt 1 A with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right (one_le_inv₀ hA |>.mpr h.le)

private theorem inv_le_maxA {A : ℝ} : A⁻¹ ≤ max A A⁻¹ := le_max_right _ _

private theorem sqrt_le_of_one_le {x y : ℝ} (hy : 1 ≤ y) (hxy : x ≤ y) : Real.sqrt x ≤ y :=
  Real.sqrt_le_iff.mpr ⟨by linarith, hxy.trans (by nlinarith)⟩

private theorem sing_integral_nonneg : 0 ≤ ∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (-(1 / 2 : ℝ)) :=
  MeasureTheory.integral_nonneg (fun ρ => by positivity)

private theorem integral_majG_le (K : ℕ) {A : ℝ} (hA : 0 < A) (B : ℝ) :
    ∫ ρ : ℝ, majG K A (B / A) ρ ≤
      (Real.exp 1 * (∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (-(1 / 2 : ℝ))) + 2 ^ (K + 1) +
          2 ^ (2 * K + 1) * (K ! : ℝ)) *
        max A A⁻¹ ^ (K + 1) * (1 + |B|) ^ (K + 1) := by
  rw [integral_majG K hA]
  set m := max A A⁻¹ with hm
  set β' := 1 + |B| with hβ'
  have hm1 : 1 ≤ m := one_le_maxA hA
  have hβ1 : 1 ≤ β' := by rw [hβ']; linarith [abs_nonneg B]
  have hm0 : 0 ≤ m := by linarith
  have hβ0 : 0 ≤ β' := by linarith
  have hmN : 1 ≤ m ^ (K + 1) := one_le_pow₀ hm1
  have hβN : 1 ≤ β' ^ (K + 1) := one_le_pow₀ hβ1
  have hc₁ := sing_integral_nonneg
  set c₁ := ∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (-(1 / 2 : ℝ)) with hc₁def

  have h1 : Real.exp 1 * c₁ ≤ Real.exp 1 * c₁ * (m ^ (K + 1) * β' ^ (K + 1)) :=
    le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hmN hβN)

  have hcBA : |B / A| ≤ β' * m := by
    rw [abs_div, abs_of_pos hA, div_eq_mul_inv]
    have h1' : |B| ≤ β' := by rw [hβ']; linarith
    have h2' : A⁻¹ ≤ m := inv_le_maxA
    exact mul_le_mul h1' h2' (inv_pos.mpr hA).le hβ0
  have hcK : 1 + |B / A| ^ K ≤ 2 * (β' ^ K * m ^ K) := by
    have : |B / A| ^ K ≤ (β' * m) ^ K := pow_le_pow_left₀ (abs_nonneg _) hcBA K
    rw [mul_pow] at this
    have hone : 1 ≤ β' ^ K * m ^ K := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hβ1) (one_le_pow₀ hm1)
    linarith

  have hsq1 : Real.sqrt (Real.pi / (Real.pi * A)) ≤ m := by
    have : Real.pi / (Real.pi * A) = A⁻¹ := by field_simp
    rw [this]
    exact sqrt_le_of_one_le hm1 inv_le_maxA

  have hpow : (2 / (Real.pi * A)) ^ K ≤ (2 * m) ^ K := by
    refine pow_le_pow_left₀ (by positivity) ?_ K
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc 2 / (Real.pi * A) ≤ 2 / (1 * A) := by
          gcongr
      _ = 2 * A⁻¹ := by ring
      _ ≤ 2 * m := by gcongr; exact inv_le_maxA

  have hsq2 : Real.sqrt (Real.pi / (Real.pi * A / 2)) ≤ 2 * m := by
    have : Real.pi / (Real.pi * A / 2) = 2 * A⁻¹ := by field_simp
    rw [this]
    exact sqrt_le_of_one_le (by linarith) (by gcongr; exact inv_le_maxA)

  have h2 : 2 ^ K * (1 + |B / A| ^ K) * Real.sqrt (Real.pi / (Real.pi * A)) ≤
      2 ^ (K + 1) * (m ^ (K + 1) * β' ^ (K + 1)) := by
    calc 2 ^ K * (1 + |B / A| ^ K) * Real.sqrt (Real.pi / (Real.pi * A))
        ≤ 2 ^ K * (2 * (β' ^ K * m ^ K)) * m := by
          gcongr
      _ = 2 ^ (K + 1) * (m ^ (K + 1) * β' ^ K) := by ring
      _ ≤ 2 ^ (K + 1) * (m ^ (K + 1) * β' ^ (K + 1)) := by
          gcongr
          all_goals first | exact hβ1 | omega

  have h3 : 2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.sqrt (Real.pi / (Real.pi * A / 2)) ≤
      2 ^ (2 * K + 1) * (K ! : ℝ) * (m ^ (K + 1) * β' ^ (K + 1)) := by
    calc 2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.sqrt (Real.pi / (Real.pi * A / 2))
        ≤ 2 ^ K * ((K ! : ℝ) * (2 * m) ^ K) * (2 * m) := by
          gcongr
      _ = 2 ^ (2 * K + 1) * (K ! : ℝ) * m ^ (K + 1) := by rw [mul_pow]; ring
      _ = 2 ^ (2 * K + 1) * (K ! : ℝ) * (m ^ (K + 1) * 1) := by ring
      _ ≤ 2 ^ (2 * K + 1) * (K ! : ℝ) * (m ^ (K + 1) * β' ^ (K + 1)) := by
          gcongr
  calc Real.exp 1 * c₁ + 2 ^ K * (1 + |B / A| ^ K) * Real.sqrt (Real.pi / (Real.pi * A)) +
        2 ^ K * ((K ! : ℝ) * (2 / (Real.pi * A)) ^ K) * Real.sqrt (Real.pi / (Real.pi * A / 2))
      ≤ Real.exp 1 * c₁ * (m ^ (K + 1) * β' ^ (K + 1)) + 2 ^ (K + 1) * (m ^ (K + 1) * β' ^ (K + 1)) +
          2 ^ (2 * K + 1) * (K ! : ℝ) * (m ^ (K + 1) * β' ^ (K + 1)) := add_le_add (add_le_add h1 h2) h3
    _ = (Real.exp 1 * c₁ + 2 ^ (K + 1) + 2 ^ (2 * K + 1) * (K ! : ℝ)) * m ^ (K + 1) * β' ^ (K + 1) := by ring

open Polynomial in

private def Bnd (n δ : ℕ) (σ₁ σ₂ : ℝ) : Prop :=
  ∃ (C M : ℝ) (N : ℕ), 0 ≤ M ∧ ∀ p : ℂ[X], p.natDegree ≤ n → ∀ A B : ℝ, 0 < A → ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ →
    ‖Epoly n δ p A (2 * Real.pi * (B : ℂ)) z‖ ≤
      C * (∑ j : Fin (n + 1), ‖p.coeff j‖) * max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) *
        Real.exp (M * |z.im|)

open Polynomial in

private theorem bnd_base (n δ : ℕ) (hδ : δ ≤ 1) (σ₂ : ℝ) : Bnd n δ (1 / 2) σ₂ := by
  obtain ⟨CΓ, MΓ, hMΓ, hΓ⟩ := exists_inv_norm_Gammaℝ_le (1 / 2 + δ) (σ₂ + δ) (by positivity)
  set K := n + ⌈σ₂⌉₊ with hK
  set C₀ : ℝ := Real.exp 1 * (∫ ρ : ℝ, Real.exp (-(1 * ρ ^ 2)) * |ρ| ^ (-(1 / 2 : ℝ))) + 2 ^ (K + 1) +
    2 ^ (2 * K + 1) * (K ! : ℝ) with hC₀
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; have := sing_integral_nonneg; positivity
  refine ⟨C₀ * CΓ, MΓ, K + 1, hMΓ, fun p hp A B hA z hz1 hz2 => ?_⟩
  have hz : 0 < z.re := by linarith
  have hS : 0 ≤ ∑ j : Fin (n + 1), ‖p.coeff j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)

  have hid := integral_prof_mul_wgt hp δ hδ hA (2 * Real.pi * (B : ℂ)) hz
  have hΓne : Complex.Gammaℝ (z + δ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.natCast_re]; positivity)
  have hE : Epoly n δ p A (2 * Real.pi * (B : ℂ)) z =
      (∫ ρ : ℝ, prof p (Real.pi * A) (2 * Real.pi * (B : ℂ)) ρ * wgt δ z ρ) / Complex.Gammaℝ (z + δ) := by
    rw [hid, mul_div_cancel_left₀ _ hΓne]
  rw [hE, norm_div, div_eq_mul_inv]

  have hint := (MeasureTheory.norm_integral_le_integral_norm _).trans
    ((integral_norm_prof_mul_wgt_le hp δ hA B hz1 hz2).trans
      (mul_le_mul_of_nonneg_left (integral_majG_le K hA B) (by positivity)))
  have hΓb : ‖Complex.Gammaℝ (z + δ)‖⁻¹ ≤ CΓ * Real.exp (MΓ * |z.im|) := by
    have h := hΓ (z + δ) (by simp only [Complex.add_re, Complex.natCast_re]; linarith)
      (by simp only [Complex.add_re, Complex.natCast_re]; linarith)
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using h
  have hCΓ : 0 ≤ CΓ * Real.exp (MΓ * |z.im|) := (inv_nonneg.mpr (norm_nonneg _)).trans hΓb
  calc ‖∫ ρ : ℝ, prof p (Real.pi * A) (2 * Real.pi * (B : ℂ)) ρ * wgt δ z ρ‖ * ‖Complex.Gammaℝ (z + δ)‖⁻¹
      ≤ (Real.exp (Real.pi * B ^ 2 / A) * (∑ j : Fin (n + 1), ‖p.coeff j‖) *
          (C₀ * max A A⁻¹ ^ (K + 1) * (1 + |B|) ^ (K + 1))) * (CΓ * Real.exp (MΓ * |z.im|)) :=
        mul_le_mul hint hΓb (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = C₀ * CΓ * (∑ j : Fin (n + 1), ‖p.coeff j‖) * max A A⁻¹ ^ (K + 1) * (1 + |B|) ^ (K + 1) *
          Real.exp (Real.pi * B ^ 2 / A) * Real.exp (MΓ * |z.im|) := by ring

private noncomputable def Emono (δ j : ℕ) (A : ℝ) (β : ℂ) (z : ℂ) : ℂ :=
  (A : ℂ) ^ (-((z + δ) / 2)) * eMono j δ (Real.pi * A)⁻¹ β ((z + δ) / 2)

private theorem differentiable_Emono (δ j : ℕ) {A : ℝ} (hA : 0 < A) (β : ℂ) : Differentiable ℂ (Emono δ j A β) := by
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  unfold Emono
  refine Differentiable.mul ?_ ?_
  · exact (differentiable_id.add_const _).div_const _ |>.neg.const_cpow (Or.inl hA0)
  · exact (differentiable_eMono j δ _ β).comp ((differentiable_id.add_const _).div_const _)

private theorem Efun_eq_sum (n δ : ℕ) (c : Fin (n + 1) → ℂ) {A : ℝ} (hA : 0 < A) (β z : ℂ) :
    Efun n δ c A β z = ∑ j : Fin (n + 1), c j * Emono δ (j : ℕ) A β z := by
  unfold Efun Emono
  rw [if_pos hA, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

open Polynomial in
private theorem Epoly_eq_sum (n δ : ℕ) (p : ℂ[X]) {A : ℝ} (hA : 0 < A) (β z : ℂ) :
    Epoly n δ p A β z = ∑ j : Fin (n + 1), p.coeff j * Emono δ (j : ℕ) A β z := by
  unfold Epoly
  exact Efun_eq_sum n δ _ hA β z

open Polynomial in
private theorem Epoly_sub (n δ : ℕ) (p q : ℂ[X]) {A : ℝ} (hA : 0 < A) (β z : ℂ) :
    Epoly n δ (p - q) A β z = Epoly n δ p A β z - Epoly n δ q A β z := by
  simp only [Epoly_eq_sum n δ _ hA β z, coeff_sub, sub_mul, Finset.sum_sub_distrib]

open Polynomial in
private theorem Epoly_C_mul (n δ : ℕ) (a : ℂ) (p : ℂ[X]) {A : ℝ} (hA : 0 < A) (β z : ℂ) :
    Epoly n δ (C a * p) A β z = a * Epoly n δ p A β z := by
  simp only [Epoly_eq_sum n δ _ hA β z, coeff_C_mul, Finset.mul_sum, mul_assoc]

open Polynomial in
private theorem Epoly_X_pow {n i : ℕ} (hi : i ≤ n) (δ : ℕ) {A : ℝ} (hA : 0 < A) (β z : ℂ) :
    Epoly n δ (X ^ i) A β z = Emono δ i A β z := by
  rw [Epoly_eq_sum n δ _ hA β z]
  rw [Finset.sum_eq_single (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (n + 1))]
  · simp [coeff_X_pow]
  · intro j _ hj
    have hji : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
    simp [coeff_X_pow, hji]
  · intro h
    exact absurd (Finset.mem_univ _) h

open Polynomial in
private theorem shiftPoly_X_pow (j : ℕ) (b : ℝ) (β : ℂ) :
    shiftPoly (X ^ j) b β = C (j : ℂ) * X ^ (j - 1) - C (2 * (b : ℂ)) * X ^ (j + 1) - C β * X ^ j := by
  unfold shiftPoly
  rw [derivative_X_pow]
  ring

open Polynomial in
private theorem Epoly_shiftPoly_X_pow (j δ : ℕ) {A : ℝ} (hA : 0 < A) (β z : ℂ) :
    Epoly (j + 1) δ (shiftPoly (X ^ j) (Real.pi * A) β) A β z =
      (j : ℂ) * Emono δ (j - 1) A β z - 2 * (Real.pi * A : ℝ) * Emono δ (j + 1) A β z - β * Emono δ j A β z := by
  rw [shiftPoly_X_pow, Epoly_sub _ _ _ _ hA, Epoly_sub _ _ _ _ hA, Epoly_C_mul _ _ _ _ hA, Epoly_C_mul _ _ _ _ hA,
    Epoly_C_mul _ _ _ _ hA, Epoly_X_pow (by omega) δ hA, Epoly_X_pow le_rfl δ hA, Epoly_X_pow (by omega) δ hA]

open Polynomial in

private theorem Emono_shift_zero (j : ℕ) {A : ℝ} (hA : 0 < A) (β z : ℂ) :
    2 * (Real.pi : ℂ) * Emono 0 j A β z =
      -((j : ℂ) * Emono 1 (j - 1) A β (z + 1) - 2 * (Real.pi * A : ℝ) * Emono 1 (j + 1) A β (z + 1) -
          β * Emono 1 j A β (z + 1)) := by
  have h := shift_zero (n := j) (p := X ^ j) (natDegree_X_pow_le j) hA β z
  rw [Epoly_X_pow le_rfl 0 hA, Epoly_shiftPoly_X_pow j 1 hA] at h
  exact h

open Polynomial in

private theorem Emono_shift_one (j : ℕ) {A : ℝ} (hA : 0 < A) (β z : ℂ) :
    z * Emono 1 j A β z =
      -((j : ℂ) * Emono 0 (j - 1) A β (z + 1) - 2 * (Real.pi * A : ℝ) * Emono 0 (j + 1) A β (z + 1) -
          β * Emono 0 j A β (z + 1)) := by
  have h := shift_one (n := j) (p := X ^ j) (natDegree_X_pow_le j) hA β z
  rw [Epoly_X_pow le_rfl 1 hA, Epoly_shiftPoly_X_pow j 0 hA] at h
  exact h

private def BndM (n δ : ℕ) (σ₁ σ₂ : ℝ) : Prop :=
  ∃ (C M : ℝ) (N : ℕ), 0 ≤ C ∧ 0 ≤ M ∧ ∀ j : ℕ, j ≤ n → ∀ A B : ℝ, 0 < A → ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ →
    ‖Emono δ j A (2 * Real.pi * (B : ℂ)) z‖ ≤
      C * max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |z.im|)

open Polynomial in
private theorem sum_norm_coeff_X_pow {n j : ℕ} (hj : j ≤ n) : ∑ i : Fin (n + 1), ‖(X ^ j : ℂ[X]).coeff i‖ = 1 := by
  rw [Finset.sum_eq_single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (n + 1))]
  · simp [coeff_X_pow]
  · intro i _ hi
    have hij : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
    simp [coeff_X_pow, hij]
  · intro h
    exact absurd (Finset.mem_univ _) h

open Polynomial in
private theorem bndM_base (n δ : ℕ) (hδ : δ ≤ 1) (σ₂ : ℝ) : BndM n δ (1 / 2) σ₂ := by
  obtain ⟨C, M, N, hM, hC⟩ := bnd_base n δ hδ σ₂
  refine ⟨|C|, M, N, abs_nonneg C, hM, fun j hj A B hA z hz1 hz2 => ?_⟩
  have h := hC (X ^ j) ((natDegree_X_pow_le j).trans hj) A B hA z hz1 hz2
  rw [Epoly_X_pow hj δ hA, sum_norm_coeff_X_pow hj, mul_one] at h
  refine h.trans ?_
  have hR : 0 ≤ max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |z.im|) := by positivity
  calc C * max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |z.im|)
      = C * (max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |z.im|)) := by ring
    _ ≤ |C| * (max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |z.im|)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hR
    _ = _ := by ring

private theorem norm_le_of_norm_le_sphere
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {K : ℝ} (hK : ∀ ζ : ℂ, ‖ζ‖ = 1 / 2 → ‖f ζ‖ ≤ K)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖f z‖ ≤ K := by
  have hr : (1 / 2 : ℝ) ≠ 0 := by norm_num
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) (1 / 2)) Metric.isBounded_ball
    hf.diffContOnCl ?_ ?_
  · intro ζ hζ
    rw [frontier_ball (0 : ℂ) hr, mem_sphere_zero_iff_norm] at hζ
    exact hK ζ hζ
  · rw [closure_ball (0 : ℂ) hr, mem_closedBall_zero_iff]
    exact hz

private noncomputable def rhs (C M : ℝ) (N : ℕ) (A B : ℝ) (w : ℂ) : ℝ :=
  C * max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |w.im|)

private theorem rhs_nonneg
    {C M : ℝ} (hC : 0 ≤ C) (N : ℕ) {A : ℝ} (hA : 0 < A) (B : ℝ) (w : ℂ) : 0 ≤ rhs C M N A B w := by
  unfold rhs
  have : 0 < max A A⁻¹ := lt_of_lt_of_le hA (le_max_left _ _)
  positivity

private theorem rhs_add_one_im (C M : ℝ) (N : ℕ) (A B : ℝ) (w : ℂ) : rhs C M N A B (w + 1) = rhs C M N A B w := by
  unfold rhs; simp

private theorem BndM_iff (n δ : ℕ) (σ₁ σ₂ : ℝ) : BndM n δ σ₁ σ₂ ↔ ∃ (C M : ℝ) (N : ℕ), 0 ≤ C ∧ 0 ≤ M ∧
    ∀ j : ℕ, j ≤ n → ∀ A B : ℝ, 0 < A → ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ →
      ‖Emono δ j A (2 * Real.pi * (B : ℂ)) z‖ ≤ rhs C M N A B z := Iff.rfl

private theorem norm_natCast_c (j : ℕ) : ‖(j : ℂ)‖ = (j : ℝ) := by
  rw [show (j : ℂ) = ((j : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg j)]

private theorem norm_two_mul_ofReal {x : ℝ} (hx : 0 ≤ x) : ‖(2 : ℂ) * (x : ℂ)‖ = 2 * x := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  simp

private theorem norm_two_pi_mul_ofReal (B : ℝ) : ‖(2 : ℂ) * (Real.pi : ℂ) * (B : ℂ)‖ = 2 * Real.pi * |B| := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  simp

private theorem coef_le {n j : ℕ} (hj : j ≤ n) {A : ℝ} (hA : 0 < A) (B : ℝ) :
    (j : ℝ) + 2 * (Real.pi * A) + 2 * Real.pi * |B| ≤ (n + 1 + 4 * Real.pi) * (max A A⁻¹ * (1 + |B|)) := by
  have hm1 : 1 ≤ max A A⁻¹ := one_le_maxA hA
  have hb1 : (1 : ℝ) ≤ 1 + |B| := by linarith [abs_nonneg B]
  have hmb : 1 ≤ max A A⁻¹ * (1 + |B|) := one_le_mul_of_one_le_of_one_le hm1 hb1
  have hj' : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hA' : A ≤ max A A⁻¹ * (1 + |B|) := (le_max_left _ _).trans (le_mul_of_one_le_right (by linarith) hb1)
  have hB' : |B| ≤ max A A⁻¹ * (1 + |B|) :=
    (by linarith : |B| ≤ 1 + |B|).trans (le_mul_of_one_le_left (by linarith) hm1)
  have e1 : (j : ℝ) ≤ (n + 1) * (max A A⁻¹ * (1 + |B|)) := by
    calc (j : ℝ) ≤ n + 1 := by linarith
      _ = (n + 1) * 1 := (mul_one _).symm
      _ ≤ (n + 1) * (max A A⁻¹ * (1 + |B|)) := mul_le_mul_of_nonneg_left hmb (by positivity)
  have e2 : 2 * (Real.pi * A) ≤ 2 * Real.pi * (max A A⁻¹ * (1 + |B|)) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hA' (by positivity)
  have e3 : 2 * Real.pi * |B| ≤ 2 * Real.pi * (max A A⁻¹ * (1 + |B|)) := mul_le_mul_of_nonneg_left hB' (by positivity)
  have := add_le_add (add_le_add e1 e2) e3
  linarith

private theorem comb_bound {n j δ' : ℕ} (hj : j ≤ n) {C M : ℝ} {N : ℕ} (hC0 : 0 ≤ C) {σ₁ σ₂' : ℝ}
    (hIH : ∀ i : ℕ, i ≤ n + 1 → ∀ A B : ℝ, 0 < A → ∀ w : ℂ, σ₁ + 1 ≤ w.re → w.re ≤ σ₂' + 1 →
      ‖Emono δ' i A (2 * Real.pi * (B : ℂ)) w‖ ≤ rhs C M N A B w)
    {A : ℝ} (hA : 0 < A) (B : ℝ) {w : ℂ} (hw1 : σ₁ ≤ w.re) (hw2 : w.re ≤ σ₂') :
    ‖(j : ℂ) * Emono δ' (j - 1) A (2 * Real.pi * (B : ℂ)) (w + 1) -
        2 * (Real.pi * A : ℝ) * Emono δ' (j + 1) A (2 * Real.pi * (B : ℂ)) (w + 1) -
          2 * Real.pi * (B : ℂ) * Emono δ' j A (2 * Real.pi * (B : ℂ)) (w + 1)‖ ≤
      rhs ((n + 1 + 4 * Real.pi) * C) M (N + 1) A B w := by
  have hre1 : σ₁ + 1 ≤ (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hre2 : (w + 1).re ≤ σ₂' + 1 := by simp only [Complex.add_re, Complex.one_re]; linarith
  have h₁ := hIH (j - 1) (by omega) A B hA (w + 1) hre1 hre2
  have h₂ := hIH (j + 1) (by omega) A B hA (w + 1) hre1 hre2
  have h₃ := hIH j (by omega) A B hA (w + 1) hre1 hre2
  rw [rhs_add_one_im] at h₁ h₂ h₃
  have hbd0 : 0 ≤ rhs C M N A B w := rhs_nonneg hC0 N hA B w
  have hcoef := coef_le hj hA B
  have hπA : (0 : ℝ) ≤ Real.pi * A := by positivity
  calc ‖(j : ℂ) * Emono δ' (j - 1) A (2 * Real.pi * (B : ℂ)) (w + 1) -
          2 * (Real.pi * A : ℝ) * Emono δ' (j + 1) A (2 * Real.pi * (B : ℂ)) (w + 1) -
            2 * Real.pi * (B : ℂ) * Emono δ' j A (2 * Real.pi * (B : ℂ)) (w + 1)‖
      ≤ ‖(j : ℂ) * Emono δ' (j - 1) A (2 * Real.pi * (B : ℂ)) (w + 1)‖ +
          ‖2 * (Real.pi * A : ℝ) * Emono δ' (j + 1) A (2 * Real.pi * (B : ℂ)) (w + 1)‖ +
            ‖2 * Real.pi * (B : ℂ) * Emono δ' j A (2 * Real.pi * (B : ℂ)) (w + 1)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = (j : ℝ) * ‖Emono δ' (j - 1) A (2 * Real.pi * (B : ℂ)) (w + 1)‖ +
          2 * (Real.pi * A) * ‖Emono δ' (j + 1) A (2 * Real.pi * (B : ℂ)) (w + 1)‖ +
            2 * Real.pi * |B| * ‖Emono δ' j A (2 * Real.pi * (B : ℂ)) (w + 1)‖ := by
        have e1 : ‖(j : ℂ) * Emono δ' (j - 1) A (2 * Real.pi * (B : ℂ)) (w + 1)‖ =
            (j : ℝ) * ‖Emono δ' (j - 1) A (2 * Real.pi * (B : ℂ)) (w + 1)‖ := by rw [norm_mul, norm_natCast_c]
        have e2 : ‖2 * (Real.pi * A : ℝ) * Emono δ' (j + 1) A (2 * Real.pi * (B : ℂ)) (w + 1)‖ =
            2 * (Real.pi * A) * ‖Emono δ' (j + 1) A (2 * Real.pi * (B : ℂ)) (w + 1)‖ := by
          rw [norm_mul, norm_two_mul_ofReal hπA]
        have e3 : ‖2 * Real.pi * (B : ℂ) * Emono δ' j A (2 * Real.pi * (B : ℂ)) (w + 1)‖ =
            2 * Real.pi * |B| * ‖Emono δ' j A (2 * Real.pi * (B : ℂ)) (w + 1)‖ := by
          rw [norm_mul, norm_two_pi_mul_ofReal]
        rw [e1, e2, e3]
    _ ≤ (j : ℝ) * rhs C M N A B w + 2 * (Real.pi * A) * rhs C M N A B w + 2 * Real.pi * |B| * rhs C M N A B w := by
        gcongr
    _ = ((j : ℝ) + 2 * (Real.pi * A) + 2 * Real.pi * |B|) * rhs C M N A B w := by ring
    _ ≤ ((n + 1 + 4 * Real.pi) * (max A A⁻¹ * (1 + |B|))) * rhs C M N A B w := mul_le_mul_of_nonneg_right hcoef hbd0
    _ = rhs ((n + 1 + 4 * Real.pi) * C) M (N + 1) A B w := by unfold rhs; ring

private theorem rhs_mono_C {C C' : ℝ} (h : C ≤ C') (M : ℝ) (N : ℕ) {A : ℝ} (hA : 0 < A) (B : ℝ) (w : ℂ) :
    rhs C M N A B w ≤ rhs C' M N A B w := by
  unfold rhs
  have hmax : 0 < max A A⁻¹ := lt_of_lt_of_le hA (le_max_left _ _)
  have : 0 ≤ max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |w.im|) := by positivity
  calc C * max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |w.im|)
      = C * (max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |w.im|)) := by ring
    _ ≤ C' * (max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |w.im|)) :=
        mul_le_mul_of_nonneg_right h this
    _ = _ := by ring

private theorem rhs_two_mul (C M : ℝ) (N : ℕ) (A B : ℝ) (w : ℂ) : 2 * rhs C M N A B w = rhs (2 * C) M N A B w := by
  unfold rhs; ring

private theorem shift_bound_even {n j : ℕ} (hj : j ≤ n) {C M : ℝ} {N : ℕ} (hC0 : 0 ≤ C) {σ₁ σ₂' : ℝ}
    (hIH : ∀ i : ℕ, i ≤ n + 1 → ∀ A B : ℝ, 0 < A → ∀ w : ℂ, σ₁ + 1 ≤ w.re → w.re ≤ σ₂' + 1 →
      ‖Emono 1 i A (2 * Real.pi * (B : ℂ)) w‖ ≤ rhs C M N A B w)
    {A : ℝ} (hA : 0 < A) (B : ℝ) {z : ℂ} (hz1 : σ₁ ≤ z.re) (hz2 : z.re ≤ σ₂') :
    ‖Emono 0 j A (2 * Real.pi * (B : ℂ)) z‖ ≤ rhs ((n + 1 + 4 * Real.pi) * C) M (N + 1) A B z := by
  have hid := Emono_shift_zero j hA (2 * Real.pi * (B : ℂ)) z
  have hc := comb_bound hj hC0 hIH hA B hz1 hz2
  have h2π : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; simp
  have hnorm : 2 * Real.pi * ‖Emono 0 j A (2 * Real.pi * (B : ℂ)) z‖ ≤
      rhs ((n + 1 + 4 * Real.pi) * C) M (N + 1) A B z := by
    rw [← h2π, ← norm_mul, hid, norm_neg]
    exact hc
  have hpi1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  exact (le_mul_of_one_le_left (norm_nonneg _) hpi1).trans hnorm

private theorem shift_bound_odd_off_disc {n j : ℕ} (hj : j ≤ n) {C M : ℝ} {N : ℕ} (hC0 : 0 ≤ C) {σ₁ σ₂' : ℝ}
    (hIH : ∀ i : ℕ, i ≤ n + 1 → ∀ A B : ℝ, 0 < A → ∀ w : ℂ, σ₁ + 1 ≤ w.re → w.re ≤ σ₂' + 1 →
      ‖Emono 0 i A (2 * Real.pi * (B : ℂ)) w‖ ≤ rhs C M N A B w)
    {A : ℝ} (hA : 0 < A) (B : ℝ) {w : ℂ} (hw1 : σ₁ ≤ w.re) (hw2 : w.re ≤ σ₂') (hw : 1 / 2 ≤ ‖w‖) :
    ‖Emono 1 j A (2 * Real.pi * (B : ℂ)) w‖ ≤ rhs (2 * ((n + 1 + 4 * Real.pi) * C)) M (N + 1) A B w := by
  have hid := Emono_shift_one j hA (2 * Real.pi * (B : ℂ)) w
  have hc := comb_bound hj hC0 hIH hA B hw1 hw2
  have hprod : ‖w‖ * ‖Emono 1 j A (2 * Real.pi * (B : ℂ)) w‖ ≤ rhs ((n + 1 + 4 * Real.pi) * C) M (N + 1) A B w := by
    rw [← norm_mul, hid, norm_neg]
    exact hc
  have hE0 : 0 ≤ ‖Emono 1 j A (2 * Real.pi * (B : ℂ)) w‖ := norm_nonneg _
  rw [← rhs_two_mul]
  calc ‖Emono 1 j A (2 * Real.pi * (B : ℂ)) w‖ = 2 * ((1 / 2) * ‖Emono 1 j A (2 * Real.pi * (B : ℂ)) w‖) := by ring
    _ ≤ 2 * (‖w‖ * ‖Emono 1 j A (2 * Real.pi * (B : ℂ)) w‖) := by gcongr
    _ ≤ 2 * rhs ((n + 1 + 4 * Real.pi) * C) M (N + 1) A B w := by linarith

private theorem shift_bound_odd {n j : ℕ} (hj : j ≤ n) {C M : ℝ} {N : ℕ} (hC0 : 0 ≤ C) (hM0 : 0 ≤ M) {σ₁ σ₂' : ℝ}
    (hσ₁ : σ₁ ≤ -(1 / 2)) (hσ₂' : 1 / 2 ≤ σ₂')
    (hIH : ∀ i : ℕ, i ≤ n + 1 → ∀ A B : ℝ, 0 < A → ∀ w : ℂ, σ₁ + 1 ≤ w.re → w.re ≤ σ₂' + 1 →
      ‖Emono 0 i A (2 * Real.pi * (B : ℂ)) w‖ ≤ rhs C M N A B w)
    {A : ℝ} (hA : 0 < A) (B : ℝ) {z : ℂ} (hz1 : σ₁ ≤ z.re) (hz2 : z.re ≤ σ₂') :
    ‖Emono 1 j A (2 * Real.pi * (B : ℂ)) z‖ ≤
      rhs (2 * ((n + 1 + 4 * Real.pi) * C) * Real.exp (M / 2)) M (N + 1) A B z := by
  have hC2 : 0 ≤ 2 * ((n + 1 + 4 * Real.pi) * C) := by positivity
  have heM : 1 ≤ Real.exp (M / 2) := Real.one_le_exp (by positivity)
  have hmonoC : 2 * ((n + 1 + 4 * Real.pi) * C) ≤ 2 * ((n + 1 + 4 * Real.pi) * C) * Real.exp (M / 2) :=
    le_mul_of_one_le_right hC2 heM
  rcases le_or_gt (1 / 2 : ℝ) ‖z‖ with hz | hz
  · exact (shift_bound_odd_off_disc hj hC0 hIH hA B hz1 hz2 hz).trans (rhs_mono_C hmonoC _ _ hA _ _)
  ·
    set Kc : ℝ := 2 * ((n + 1 + 4 * Real.pi) * C) * Real.exp (M / 2) * max A A⁻¹ ^ (N + 1) * (1 + |B|) ^ (N + 1) *
      Real.exp (Real.pi * B ^ 2 / A) with hKc
    have hK0 : 0 ≤ Kc := by rw [hKc]; positivity
    have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 / 2 → ‖Emono 1 j A (2 * Real.pi * (B : ℂ)) ζ‖ ≤ Kc := by
      intro ζ hζ
      have hre : |ζ.re| ≤ 1 / 2 := hζ ▸ Complex.abs_re_le_norm ζ
      have him : |ζ.im| ≤ 1 / 2 := hζ ▸ Complex.abs_im_le_norm ζ
      have hζ1 : σ₁ ≤ ζ.re := by linarith [(abs_le.mp hre).1]
      have hζ2 : ζ.re ≤ σ₂' := by linarith [(abs_le.mp hre).2]
      have hexp : Real.exp (M * |ζ.im|) ≤ Real.exp (M / 2) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg ζ.im])
      refine (shift_bound_odd_off_disc hj hC0 hIH hA B hζ1 hζ2 hζ.ge).trans ?_
      unfold rhs
      rw [hKc]
      have : 0 ≤ 2 * ((n + 1 + 4 * Real.pi) * C) * max A A⁻¹ ^ (N + 1) * (1 + |B|) ^ (N + 1) *
          Real.exp (Real.pi * B ^ 2 / A) := by
        positivity
      calc 2 * ((n + 1 + 4 * Real.pi) * C) * max A A⁻¹ ^ (N + 1) * (1 + |B|) ^ (N + 1) *
            Real.exp (Real.pi * B ^ 2 / A) *
            Real.exp (M * |ζ.im|)
          ≤ 2 * ((n + 1 + 4 * Real.pi) * C) * max A A⁻¹ ^ (N + 1) * (1 + |B|) ^ (N + 1) *
            Real.exp (Real.pi * B ^ 2 / A) *
            Real.exp (M / 2) := mul_le_mul_of_nonneg_left hexp this
        _ = _ := by ring
    have hdisc := norm_le_of_norm_le_sphere (differentiable_Emono 1 j hA _) hcirc hz.le
    refine hdisc.trans ?_
    unfold rhs
    rw [hKc]
    exact le_mul_of_one_le_right hK0 (Real.one_le_exp (by positivity))

private theorem bndM_shift (n δ : ℕ) (hδ : δ ≤ 1) {σ₁ σ₂ : ℝ} (hσ₁ : σ₁ ≤ -(1 / 2))
    (ih : BndM (n + 1) (1 - δ) (σ₁ + 1) (max σ₂ (1 / 2) + 1)) : BndM n δ σ₁ σ₂ := by
  obtain ⟨C, M, N, hC0, hM0, hIH⟩ := ih
  have hσ₂' : (1 / 2 : ℝ) ≤ max σ₂ (1 / 2) := le_max_right _ _
  have hσ₂le : σ₂ ≤ max σ₂ (1 / 2) := le_max_left _ _
  have hC2 : 0 ≤ 2 * ((n + 1 + 4 * Real.pi) * C) * Real.exp (M / 2) := by positivity
  refine ⟨2 * ((n + 1 + 4 * Real.pi) * C) * Real.exp (M / 2), M, N + 1, hC2, hM0, fun j hj A B hA z hz1 hz2 => ?_⟩
  have hz2' : z.re ≤ max σ₂ (1 / 2) := hz2.trans hσ₂le
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hδ with rfl | rfl
  ·
    simp only [Nat.sub_zero] at hIH
    have h := shift_bound_even hj hC0 hIH hA B hz1 hz2'
    refine h.trans (rhs_mono_C ?_ _ _ hA _ _)
    have heM : 1 ≤ Real.exp (M / 2) := Real.one_le_exp (by positivity)
    have h0 : 0 ≤ (n + 1 + 4 * Real.pi) * C := by positivity
    nlinarith
  ·
    simp only [Nat.sub_self] at hIH
    exact shift_bound_odd hj hC0 hM0 hσ₁ hσ₂' hIH hA B hz1 hz2'

private theorem bndM_all (k : ℕ) : ∀ n δ : ℕ, δ ≤ 1 → ∀ σ₂ : ℝ, BndM n δ (1 / 2 - k) σ₂ := by
  induction k with
  | zero =>
    intro n δ hδ σ₂
    simpa using bndM_base n δ hδ σ₂
  | succ k ihk =>
    intro n δ hδ σ₂
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine bndM_shift n δ hδ (by push_cast; linarith) ?_
    have hcast : (1 / 2 : ℝ) - ((k + 1 : ℕ) : ℝ) + 1 = 1 / 2 - (k : ℝ) := by push_cast; ring
    rw [hcast]
    exact ihk (n + 1) (1 - δ) (by omega) (max σ₂ (1 / 2) + 1)

private theorem conj3 (n δ : ℕ) (hδ : δ ≤ 1) (σ₁ σ₂ : ℝ) :
    ∃ (C M : ℝ) (N : ℕ), ∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), 0 < A → ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ →
      ‖Efun n δ c A (2 * Real.pi * (B : ℂ)) z‖ ≤
        C * (∑ j : Fin (n + 1), ‖c j‖) * max A A⁻¹ ^ N * (1 + |B|) ^ N * Real.exp (Real.pi * B ^ 2 / A) *
          Real.exp (M * |z.im|) := by
  obtain ⟨C, M, N, -, -, hB⟩ := bndM_all ⌈1 / 2 - σ₁⌉₊ n δ hδ σ₂
  refine ⟨C, M, N, fun c A B hA z hz1 hz2 => ?_⟩
  have hz1' : 1 / 2 - (⌈1 / 2 - σ₁⌉₊ : ℝ) ≤ z.re := by linarith [Nat.le_ceil (1 / 2 - σ₁)]
  rw [Efun_eq_sum n δ c hA]
  calc ‖∑ j : Fin (n + 1), c j * Emono δ (j : ℕ) A (2 * Real.pi * (B : ℂ)) z‖
      ≤ ∑ j : Fin (n + 1), ‖c j‖ * ‖Emono δ (j : ℕ) A (2 * Real.pi * (B : ℂ)) z‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ ∑ j : Fin (n + 1), ‖c j‖ * rhs C M N A B z := by
        gcongr with j _
        exact hB j (Nat.lt_succ_iff.mp j.2) A B hA z hz1' hz2
    _ = (∑ j : Fin (n + 1), ‖c j‖) * rhs C M N A B z := by rw [Finset.sum_mul]
    _ = _ := by unfold rhs; ring

end PolyGaussTate

theorem solution (n δ : ℕ) (hδ : δ ≤ 1) :
    ∃ E : (Fin (n + 1) → ℂ) → ℝ → ℝ → ℂ → ℂ,
      (∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), Differentiable ℂ (E c A B)) ∧
      (∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), 0 < A → ∀ z : ℂ, 0 < z.re →
        ∫ ρ : ℝ, (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) *
            (Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ) * (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1) =
          Complex.Gammaℝ (z + δ) * E c A B z) ∧
      (∀ σ₁ σ₂ : ℝ, ∃ (C M : ℝ) (N : ℕ), ∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), 0 < A → ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ →
        ‖E c A B z‖ ≤ C * (∑ j : Fin (n + 1), ‖c j‖) * max A A⁻¹ ^ N * (1 + |B|) ^ N *
          Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |z.im|)) ∧
      (∀ z : ℂ, ContinuousOn (fun p : (Fin (n + 1) → ℂ) × ℝ × ℝ => E p.1 p.2.1 p.2.2 z)
        {p : (Fin (n + 1) → ℂ) × ℝ × ℝ | 0 < p.2.1}) := by
  refine ⟨fun c A B => PolyGaussTate.Efun n δ c A (2 * Real.pi * (B : ℂ)), ?_, ?_, ?_, ?_⟩
  · intro c A B
    exact PolyGaussTate.differentiable_Efun n δ c A _
  · intro c A B hA z hz
    simp_rw [PolyGaussTate.integrand_eq n δ c A B z]
    exact PolyGaussTate.integral_eq_Gammaℝ_mul_Efun n δ hδ c hA _ hz
  · exact PolyGaussTate.conj3 n δ hδ
  · intro z
    exact PolyGaussTate.continuousOn_Efun n δ z

end S_exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul
end P2MW
export P2MW.S_exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul (solution)
