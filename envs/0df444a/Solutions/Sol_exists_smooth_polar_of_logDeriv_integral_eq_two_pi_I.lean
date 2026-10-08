-- Prove2me | solution 1 for exists_smooth_polar_of_logDeriv_integral_eq_two_pi_I
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T19:07:39.725681+00:00
-- url     : https://prove2.me/submissions/7d1d916f-ed07-4fe8-abe5-62c2c45e59ca

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod

open scoped ContDiff
open Complex MeasureTheory Set

namespace HryniewiczCriterion

/-- `e i` is the `i`-th standard basis vector of `ℝ⁴`. -/
lemma clm_apply_eq_sum (L : R4 →L[ℝ] ℝ) (v : R4) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) +
      v 2 * L (Pi.single 2 1) + v 3 * L (Pi.single 3 1) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_smul, Fin.sum_univ_four, smul_eq_mul]

/-- The linear map `L ↦ J ∇L`: `jvec L = (-L e₁, L e₀, -L e₃, L e₂)`. -/
noncomputable def jvec : (R4 →L[ℝ] ℝ) →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun i =>
    ![-(ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 0 1 : R4),
      -(ContinuousLinearMap.apply ℝ ℝ (Pi.single 3 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 2 1 : R4)] i

lemma jvec_apply (L : R4 →L[ℝ] ℝ) :
    jvec L = ![-L (Pi.single 1 1), L (Pi.single 0 1), -L (Pi.single 3 1), L (Pi.single 2 1)] := by
  ext i; fin_cases i <;> simp [jvec]

lemma hamiltonianVectorField_eq (H : R4 → ℝ) :
    hamiltonianVectorField H = fun y => jvec (fderiv ℝ H y) := by
  funext y; rw [jvec_apply]; rfl

lemma omega0_jvec_left (L : R4 →L[ℝ] ℝ) (q : R4) : omega0 (jvec L) q = -L q := by
  rw [clm_apply_eq_sum L q, jvec_apply]; simp [omega0]; ring

lemma omega0_jvec_right (L : R4 →L[ℝ] ℝ) (p : R4) : omega0 p (jvec L) = L p := by
  rw [clm_apply_eq_sum L p, jvec_apply]; simp [omega0] <;> ring

lemma apply_jvec_add (L M : R4 →L[ℝ] ℝ) : L (jvec M) + M (jvec L) = 0 := by
  rw [clm_apply_eq_sum L, clm_apply_eq_sum M, jvec_apply, jvec_apply]; simp; ring

lemma apply_jvec_self (L : R4 →L[ℝ] ℝ) : L (jvec L) = 0 := by
  have := apply_jvec_add L L; linarith

lemma liouvilleForm_eq (x v : R4) : liouvilleForm x v = omega0 x v / 2 := by
  simp [liouvilleForm, omega0]

lemma omega0_antisymm (u v : R4) : omega0 u v = -omega0 v u := by
  simp [omega0]; ring

lemma omega0_self (u : R4) : omega0 u u = 0 := by
  simp [omega0]; ring

lemma omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma omega0_lin_left (u a b : R4) (p q : ℝ) :
    omega0 (p • a + q • b) u = p * omega0 a u + q * omega0 b u := by
  simp [omega0]; ring

lemma omega0_smul_smul (u v : R4) (p q : ℝ) : omega0 (p • u) (q • v) = p * q * omega0 u v := by
  simp [omega0]; ring

/-- A symplectic pair `Z₁, Z₂` together with an `ω₀`-orthogonal symplectic pair `a, b`
spans `ℝ⁴`; every `v` that is `ω₀`-orthogonal to `a, b` lies in `span (Z₁, Z₂)`. -/
lemma eq_frame_of_omega0 (Z₁ Z₂ a b v : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0) :
    v = omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by
  set w : Fin 4 → R4 := ![Z₁, Z₂, a, b] with hw
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    replace hg : g 0 • Z₁ + g 1 • Z₂ + g 2 • a + g 3 • b = 0 := by
      simpa [Fin.sum_univ_four, hw] using hg
    have e1 := congrArg (omega0 Z₁) hg
    have e2 := congrArg (omega0 Z₂) hg
    have e3 := congrArg (omega0 a) hg
    have e4 := congrArg (omega0 b) hg
    rw [omega0_lin_right] at e1 e2 e3 e4
    have z : ∀ u : R4, omega0 u 0 = 0 := fun u => by simp [omega0]
    rw [z] at e1 e2 e3 e4
    rw [omega0_self, h12, h1a, h1b] at e1
    rw [omega0_antisymm Z₂ Z₁, h12, omega0_self, h2a, h2b] at e2
    rw [omega0_antisymm a Z₁, omega0_antisymm a Z₂, h1a, h2a, omega0_self] at e3
    rw [omega0_antisymm b Z₁, omega0_antisymm b Z₂, omega0_antisymm b a, h1b, h2b,
      omega0_self] at e4
    have g1 : g 1 = 0 := by linarith
    have g0 : g 0 = 0 := by linarith
    have g3 : g 3 = 0 := by
      have : g 3 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    have g2 : g 2 = 0 := by
      have : g 2 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    intro i; fin_cases i <;> assumption
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℝ (Set.range w) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  replace hc : c 0 • Z₁ + c 1 • Z₂ + c 2 • a + c 3 • b = v := by
    simpa [Fin.sum_univ_four, hw] using hc
  -- pair with `a` and `b` to kill the last two coefficients
  have ea : omega0 v a = c 0 * omega0 Z₁ a + c 1 * omega0 Z₂ a + c 2 * omega0 a a +
      c 3 * omega0 b a := by
    rw [← hc, omega0_antisymm, omega0_lin_right]
    rw [omega0_antisymm a Z₁, omega0_antisymm a Z₂, omega0_antisymm a b, omega0_self]; ring
  have eb : omega0 v b = c 0 * omega0 Z₁ b + c 1 * omega0 Z₂ b + c 2 * omega0 a b +
      c 3 * omega0 b b := by
    rw [← hc, omega0_antisymm, omega0_lin_right]
    rw [omega0_antisymm b Z₁, omega0_antisymm b Z₂, omega0_antisymm b a, omega0_self]; ring
  rw [h1a, h2a, omega0_self, omega0_antisymm b a, hva] at ea
  rw [h1b, h2b, omega0_self, hvb] at eb
  have c3 : c 3 = 0 := by
    have : c 3 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have c2 : c 2 = 0 := by
    have : c 2 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have hv2 : v = c 0 • Z₁ + c 1 • Z₂ := by rw [← hc, c2, c3]; simp
  have k0 : omega0 v Z₂ = c 0 := by
    rw [hv2, omega0_lin_left, omega0_self, h12]; ring
  have k1 : omega0 Z₁ v = c 1 := by
    rw [hv2, omega0_antisymm, omega0_lin_left, omega0_self, omega0_antisymm Z₂ Z₁, h12]; ring
  rw [k0, k1]; exact hv2

/-- In the situation of `eq_frame_of_omega0`, `ω₀` on two such vectors is the
determinant of their `(Z₁, Z₂)`-coordinates. -/
lemma omega0_eq_det_of_frame (Z₁ Z₂ a b v w : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0)
    (hwa : omega0 w a = 0) (hwb : omega0 w b = 0) :
    omega0 v w = omega0 v Z₂ * omega0 Z₁ w - omega0 w Z₂ * omega0 Z₁ v := by
  have hv := eq_frame_of_omega0 Z₁ Z₂ a b v h12 h1a h1b h2a h2b hab hva hvb
  have hw := eq_frame_of_omega0 Z₁ Z₂ a b w h12 h1a h1b h2a h2b hab hwa hwb
  set p := omega0 v Z₂; set q := omega0 Z₁ v
  set r := omega0 w Z₂; set s := omega0 Z₁ w
  rw [hv, hw]
  simp only [omega0] at h12 ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (p * s - r * q) * h12

end HryniewiczCriterion

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

lemma contDiff_fderiv_of_smooth (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (fderiv ℝ H) :=
  hH.fderiv_right le_rfl

lemma contDiff_fderiv2_of_smooth (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ H)) :=
  (contDiff_fderiv_of_smooth hH).fderiv_right le_rfl

lemma hasFDerivAt_hvf (hH : ContDiff ℝ ∞ H) (y : R4) :
    HasFDerivAt (hamiltonianVectorField H) (jvec.comp (fderiv ℝ (fderiv ℝ H) y)) y := by
  rw [hamiltonianVectorField_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ H) y :=
    (contDiff_fderiv_of_smooth hH).differentiable (by simp) y
  exact jvec.hasFDerivAt.comp y hd.hasFDerivAt

lemma fderiv_hvf (hH : ContDiff ℝ ∞ H) (y : R4) :
    fderiv ℝ (hamiltonianVectorField H) y = jvec.comp (fderiv ℝ (fderiv ℝ H) y) :=
  (hasFDerivAt_hvf hH y).fderiv

lemma D2_symm (hH : ContDiff ℝ ∞ H) (y v w : R4) :
    fderiv ℝ (fderiv ℝ H) y v w = fderiv ℝ (fderiv ℝ H) y w v :=
  hH.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 le_top) v w

lemma contDiff_hvf (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (hamiltonianVectorField H) := by
  rw [hamiltonianVectorField_eq]
  exact jvec.contDiff.comp (contDiff_fderiv_of_smooth hH)

/-- Bootstrapping: a solution of `f' = g` with `g` as smooth as `f` is `C^∞`. -/
lemma contDiff_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ n : ℕ, ContDiff ℝ n f → ContDiff ℝ n g) : ContDiff ℝ ∞ f := by
  rw [contDiff_infty]
  intro n
  induction n with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hf t).continuousAt)
  | succ n ih =>
    have hd : deriv f = g := funext fun t => (hf t).deriv
    have h := contDiff_succ_iff_deriv (𝕜 := ℝ) (f := f) (n := (n : ℕ∞ω))
    push_cast
    refine h.2 ⟨fun t => (hf t).differentiableAt, by simp, ?_⟩
    rw [hd]; exact hg n ih

lemma trajectory_contDiff (hH : ContDiff ℝ ∞ H) {x : ℝ → R4} (hx : IsTrajectory H x) :
    ContDiff ℝ ∞ x :=
  contDiff_of_hasDerivAt hx.1 fun n hn =>
    ((contDiff_hvf hH).of_le (by exact_mod_cast le_top)).comp hn

lemma linearizedFlow_contDiff (hH : ContDiff ℝ ∞ H) {x : ℝ → R4} (hx : IsTrajectory H x)
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) : ContDiff ℝ ∞ Y := by
  refine contDiff_of_hasDerivAt hY.2 fun n hn => ?_
  have hA : ContDiff ℝ ∞ fun t => fderiv ℝ (hamiltonianVectorField H) (x t) := by
    simp_rw [fderiv_hvf hH]
    exact contDiff_const.clm_comp
      ((contDiff_fderiv2_of_smooth hH).comp (trajectory_contDiff hH hx))
  exact (hA.of_le (by exact_mod_cast le_top)).clm_comp hn

lemma linearizedFlow_hasDerivAt (hH : ContDiff ℝ ∞ H) {x : ℝ → R4}
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (u : R4) (t : ℝ) :
    HasDerivAt (fun t => Y t u) (jvec (fderiv ℝ (fderiv ℝ H) (x t) (Y t u))) t := by
  have h := (hY.2 t).clm_apply (hasDerivAt_const t u)
  simpa [fderiv_hvf hH] using h

/-- The linearized Hamiltonian flow is symplectic. -/
lemma omega0_linearizedFlow (hH : ContDiff ℝ ∞ H) {x : ℝ → R4}
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (u v : R4) (t : ℝ) :
    omega0 (Y t u) (Y t v) = omega0 u v := by
  set g : ℝ → ℝ := fun t => omega0 (Y t u) (Y t v) with hg
  have hder : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h := fun i => hasDerivAt_pi.1 (linearizedFlow_hasDerivAt hH hY u s) i
    have k := fun i => hasDerivAt_pi.1 (linearizedFlow_hasDerivAt hH hY v s) i
    have key := ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub
      ((h 3).mul (k 2))
    have hval : omega0 (jvec (fderiv ℝ (fderiv ℝ H) (x s) (Y s u))) (Y s v) +
        omega0 (Y s u) (jvec (fderiv ℝ (fderiv ℝ H) (x s) (Y s v))) = 0 := by
      rw [omega0_jvec_left, omega0_jvec_right, D2_symm hH]; ring
    have key2 := key.congr_of_eventuallyEq (f₁ := g)
      (Filter.Eventually.of_forall fun r => by simp [hg, omega0])
    exact key2.congr_deriv (by rw [← hval]; simp only [omega0]; ring)
  have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simp only [hg] at hc
  rw [hc, hY.1]; rfl

/-- The linearized flow preserves `dH`: it maps `T_{x(0)} S` to `T_{x(t)} S`. -/
lemma dH_linearizedFlow (hH : ContDiff ℝ ∞ H) {x : ℝ → R4} (hx : IsTrajectory H x)
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (v : R4) (t : ℝ) :
    fderiv ℝ H (x t) (Y t v) = fderiv ℝ H (x 0) v := by
  set f : ℝ → ℝ := fun t => fderiv ℝ H (x t) (Y t v) with hf
  have hder : ∀ s, HasDerivAt f 0 s := by
    intro s
    have hd : DifferentiableAt ℝ (fderiv ℝ H) (x s) :=
      (contDiff_fderiv_of_smooth hH).differentiable (by simp) (x s)
    have h1 := hd.hasFDerivAt.comp_hasDerivAt s (hx.1 s)
    have h2 := h1.clm_apply (linearizedFlow_hasDerivAt hH hY v s)
    refine h2.congr_deriv ?_
    rw [hamiltonianVectorField_eq, Function.comp_apply]
    rw [D2_symm hH, add_comm]
    exact apply_jvec_add _ _
  have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simp only [hf] at hc
  rw [hc, hY.1]; rfl

end HryniewiczCriterion

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

/-!
# Smooth polar lifts of loops, Fubini for continuous integrands, and the action identity
-/


noncomputable section

namespace WindA

/-- Fubini on `[0,1]²` for a continuous integrand. -/
lemma integral_integral_swap_unit {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f x y = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f x y := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  apply MeasureTheory.integral_integral_swap
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- A smooth closed loop in `ℂ \ {0}` with winding number one has a smooth polar form
`c = r e^{iθ}` with `r > 0` periodic and `θ(s + 1) = θ(s) + 2π`. -/
lemma exists_polar_of_winding_one {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hne : ∀ s, c s ≠ 0)
    (hper : ∀ s, c (s + 1) = c s)
    (hW : ∫ s in (0 : ℝ)..1, deriv c s / c s = 2 * Real.pi * I) :
    ∃ r θ : ℝ → ℝ, ContDiff ℝ ∞ r ∧ ContDiff ℝ ∞ θ ∧ (∀ s, 0 < r s) ∧
      (∀ s, r (s + 1) = r s) ∧ (∀ s, θ (s + 1) = θ s + 2 * Real.pi) ∧
      ∀ s, c s = (r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * I) := by
  have hd : ∀ t, HasDerivAt c (deriv c t) t := fun t =>
    ((hc.differentiable (by simp)) t).hasDerivAt
  have hdc : ContDiff ℝ ∞ (deriv c) := hc.iterate_deriv 1
  have hq : ContDiff ℝ ∞ fun s => deriv c s / c s := by
    simp only [div_eq_mul_inv]; exact hdc.mul (hc.inv hne)
  set L : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, deriv c s / c s
  have hL : ∀ t, HasDerivAt L (deriv c t / c t) t := fun t =>
    (hq.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hLs : ContDiff ℝ ∞ L :=
    HryniewiczCriterion.contDiff_of_hasDerivAt hL fun n _ => hq.of_le (by exact_mod_cast le_top)
  have hexp := eq_mul_exp_integral hd hdc.continuous hne
  set r : ℝ → ℝ := fun s => ‖c 0‖ * Real.exp (L s).re
  set θ : ℝ → ℝ := fun s => arg (c 0) + (L s).im
  have hexp' : ∀ t, c t = c 0 * exp (L t) := hexp
  have hpolar : ∀ s, c s = (r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * I) := by
    intro s
    have e1 : exp (L s) = (Real.exp (L s).re : ℂ) * exp (((L s).im : ℂ) * I) := by
      conv_lhs => rw [← Complex.re_add_im (L s)]
      rw [Complex.exp_add, Complex.ofReal_exp]
    have e2 := norm_mul_exp_arg_mul_I (c 0)
    rw [← Complex.exp_ofReal_mul_I, hexp' s, e1]
    conv_lhs => rw [← e2]
    simp only [r, θ]
    push_cast
    rw [show ((arg (c 0) : ℂ) + ((L s).im : ℂ)) * I = (arg (c 0) : ℂ) * I + ((L s).im : ℂ) * I by ring,
      Complex.exp_add]
    ring
  have hrpos : ∀ s, 0 < r s := fun s => mul_pos (norm_pos_iff.2 (hne 0)) (Real.exp_pos _)
  have hnorm : ∀ s, ‖c s‖ = r s := by
    intro s
    rw [hpolar s, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hrpos s).le,
      ← Complex.exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hqper : Function.Periodic (fun s => deriv c s / c s) 1 := by
    intro s
    have : deriv c (s + 1) = deriv c s := by
      have h1 : (fun t => c (t + 1)) = c := funext hper
      have := deriv_comp_add_const (f := c) (a := 1) (x := s)
      rw [h1] at this; exact this.symm
    simp only [this, hper]
  have hLper : ∀ s, L (s + 1) = L s + 2 * Real.pi * I := by
    intro s
    have := hqper.intervalIntegral_add_eq_add 0 s (fun a b => hq.continuous.intervalIntegrable a b)
    simp only [zero_add] at this
    simp only [L]; rw [this, hW]
  refine ⟨r, θ, ?_, ?_, hrpos, ?_, ?_, hpolar⟩
  · exact contDiff_const.mul (Real.contDiff_exp.comp (Complex.reCLM.contDiff.comp hLs))
  · exact contDiff_const.add (Complex.imCLM.contDiff.comp hLs)
  · intro s; rw [← hnorm, ← hnorm, hper]
  · intro s; simp only [θ, hLper]; simp; ring

end WindA

theorem solution {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hne : ∀ s, c s ≠ 0)
    (hper : ∀ s, c (s + 1) = c s)
    (hW : ∫ s in (0 : ℝ)..1, deriv c s / c s = 2 * Real.pi * Complex.I) :
    ∃ r θ : ℝ → ℝ, ContDiff ℝ ∞ r ∧ ContDiff ℝ ∞ θ ∧ (∀ s, 0 < r s) ∧
      (∀ s, r (s + 1) = r s) ∧ (∀ s, θ (s + 1) = θ s + 2 * Real.pi) ∧
      ∀ s, c s = (r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * Complex.I) :=
  WindA.exists_polar_of_winding_one hc hne hper hW
