-- Prove2me | solution 2 for limiting_fourier_lim1_aux
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:39.8587+00:00
-- url     : https://prove2.me/submissions/b4c7b502-6b8d-413d-b459-5bb30d98fadc

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
import Definitions.Def_PrimeNumberTheoremAnd_SmoothExistence
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Definitions.Def_PrimeNumberTheoremAnd_Wiener
set_option autoImplicit true
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate
variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]
attribute [fun_prop] Real.continuous_fourierChar
attribute [fun_prop] measurable_coe_nnreal_ennreal

theorem PNAux.gg_antitoneOn {x : ℝ} (hx : 0 < x) : AntitoneOn (gg x) (Ici x) := by
  intro y hy z hz hyz
  simp only [mem_Ici] at hy hz
  have hy0 : 0 < y := lt_of_lt_of_le hx hy
  have hlog : 0 ≤ Real.log (y / x) := Real.log_nonneg ((one_le_div hx).mpr hy)
  have hlog' : Real.log (y / x) ≤ Real.log (z / x) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hc : 0 ≤ 1 / (2 * π) := by positivity
  have h1 : 1 + (1 / (2 * π) * Real.log (y / x)) ^ 2 ≤ 1 + (1 / (2 * π) * Real.log (z / x)) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlog' hc
    have h0 : 0 ≤ 1 / (2 * π) * Real.log (y / x) := mul_nonneg hc hlog
    nlinarith
  unfold gg
  exact mul_le_mul (one_div_le_one_div_of_le hy0 hyz) (inv_anti₀ (by positivity) h1)
    (by positivity) (by positivity)

theorem PNAux.gg_nonneg {x y : ℝ} (hy : 0 ≤ y) : 0 ≤ gg x y := by
  unfold gg
  positivity

theorem PNAux.hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by
  set F : ℝ → ℝ := fun t ↦ a * hh b (t / c) with hF
  have himg : (fun s : ℝ => c * Real.exp s) '' Set.univ = Ioi 0 := by
    ext y
    simp only [Set.image_univ, Set.mem_range, mem_Ioi]
    constructor
    · rintro ⟨s, rfl⟩; positivity
    · intro hy
      exact ⟨Real.log (y / c), by rw [Real.exp_log (by positivity)]; field_simp⟩
  have hder : ∀ s ∈ (Set.univ : Set ℝ), HasDerivWithinAt (fun s : ℝ => c * Real.exp s)
      (c * Real.exp s) Set.univ s := fun s _ =>
    ((Real.hasDerivAt_exp s).const_mul c).hasDerivWithinAt
  have hinj : Set.InjOn (fun s : ℝ => c * Real.exp s) Set.univ := by
    intro x _ y _ h
    simpa [hc.ne'] using h
  have hpt : ∀ s : ℝ, |c * Real.exp s| • F (c * Real.exp s) = a * c * (1 + (b * s) ^ 2)⁻¹ := by
    intro s
    have : c * Real.exp s / c = Real.exp s := by field_simp
    simp only [hF, this, hh, Real.log_exp, smul_eq_mul]
    rw [abs_of_pos (by positivity)]
    have : (1 + (b * s) ^ 2) ≠ 0 := by positivity
    field_simp
  have hI : MeasureTheory.Integrable (fun s : ℝ => a * c * (1 + (b * s) ^ 2)⁻¹) := by
    have := (integrable_inv_one_add_sq).comp_mul_left' (g := fun x : ℝ => (1 + x ^ 2)⁻¹)
      hb.ne'
    exact this.const_mul (a * c)
  have hint : IntegrableOn F (Ioi 0) := by
    rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj]
    simp_rw [hpt]
    exact hI.integrableOn
  refine ⟨?_, ?_⟩
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact hint
  · show ∫ t in Ioi 0, F t = _
    rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder hinj]
    simp_rw [hpt]
    rw [Measure.restrict_univ, integral_const_mul,
      Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) b, integral_univ_inv_one_add_sq]
    simp only [smul_eq_mul, abs_inv, abs_of_pos hb]
    field_simp

theorem PNAux.gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  unfold gg hh
  by_cases hi : i = 0
  · simp [hi]
  · have h1 : (1 + (1 / (2 * π) * Real.log (i / x)) ^ 2) ≠ 0 := by positivity
    field_simp

theorem PNAux.integrableOn_gg {x : ℝ} (hx : 0 < x) : IntegrableOn (gg x) (Ioi 0) := by
  have h := (PNAux.hh_integral (a := x⁻¹) (b := 1 / (2 * π)) (c := x) (by positivity)
    (by positivity) hx).1
  have h' : IntegrableOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioi 0) :=
    h.mono_set Ioi_subset_Ici_self
  refine h'.congr_fun (fun t _ => ?_) measurableSet_Ioi
  exact (PNAux.gg_of_hh hx.ne' t).symm

theorem PNAux.summable_gg_shift {x : ℝ} (hx : 0 < x) :
    Summable (fun i : ℕ => gg x ((⌈x⌉₊ : ℝ) + ((i + 1 : ℕ) : ℝ))) := by
  set y0 : ℝ := (⌈x⌉₊ : ℝ) with hy0
  have hxy : x ≤ y0 := Nat.le_ceil x
  have hint := PNAux.integrableOn_gg hx
  apply summable_of_sum_range_le (c := ∫ t in Ioi 0, gg x t)
  · intro i; exact PNAux.gg_nonneg (by positivity)
  · intro M
    have hanti : AntitoneOn (gg x) (Icc y0 (y0 + M)) :=
      (PNAux.gg_antitoneOn hx).mono (fun t ht => le_trans hxy ht.1)
    have h1 := hanti.sum_le_integral
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)])]
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun t ht => PNAux.gg_nonneg (le_of_lt ht))
    · have hsub : Ioc y0 (y0 + M) ⊆ Ioi 0 := fun t ht =>
        lt_of_lt_of_le (lt_of_lt_of_le hx hxy) ht.1.le
      exact hsub.eventuallyLE

theorem PNAux.abel_bound (a g : ℕ → ℝ) (K : ℝ)
    (hA : ∀ n, ∑ i ∈ Finset.range n, a i ≤ K * n) (hg : Antitone g) :
    ∀ N, ∑ n ∈ Finset.range N, a n * g n + (K * N - ∑ i ∈ Finset.range N, a i) * g N
      ≤ K * ∑ n ∈ Finset.range N, g n := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    have hD : 0 ≤ K * ((N + 1 : ℕ) : ℝ) - (∑ i ∈ Finset.range N, a i + a N) := by
      have := hA (N + 1)
      rw [Finset.sum_range_succ] at this
      linarith
    have hgm : g (N + 1) ≤ g N := hg (Nat.le_succ N)
    push_cast at hD ⊢
    nlinarith [mul_le_mul_of_nonneg_left hgm hD]

theorem PNAux.abel_sum_le (a g : ℕ → ℝ) (K : ℝ)
    (hA : ∀ n, ∑ i ∈ Finset.range n, a i ≤ K * n) (hg : Antitone g) (hg0 : ∀ n, 0 ≤ g n)
    (N : ℕ) : ∑ n ∈ Finset.range N, a n * g n ≤ K * ∑ n ∈ Finset.range N, g n := by
  have h1 := PNAux.abel_bound a g K hA hg N
  have h2 : 0 ≤ (K * N - ∑ i ∈ Finset.range N, a i) * g N :=
    mul_nonneg (by linarith [hA N]) (hg0 N)
  linarith

theorem PNAux.summable_gg_mul {f : ℕ → ℂ}
    (hcheby : (∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(f k : ℂ)‖) n ≤ C * n))
    {x : ℝ} (hx : 0 < x) : Summable fun n : ℕ => ‖f n‖ * gg x n := by
  obtain ⟨C, hC⟩ := hcheby
  set N0 : ℕ := ⌈x⌉₊ with hN0
  have hxy : x ≤ (N0 : ℝ) := Nat.le_ceil x
  set g : ℕ → ℝ := fun n => gg x ((max n N0 : ℕ) : ℝ) with hg
  have hmem : ∀ n : ℕ, ((max n N0 : ℕ) : ℝ) ∈ Ici x := fun n => by
    simp only [mem_Ici]
    exact le_trans hxy (by exact_mod_cast le_max_right n N0)
  have hanti : Antitone g := fun n m hnm =>
    PNAux.gg_antitoneOn hx (hmem n) (hmem m) (by exact_mod_cast max_le_max hnm le_rfl)
  have hg0 : ∀ n, 0 ≤ g n := fun n => PNAux.gg_nonneg (Nat.cast_nonneg _)
  have hgs : Summable g := by
    have h1 := PNAux.summable_gg_shift hx
    rw [← summable_nat_add_iff (N0 + 1)]
    refine h1.congr (fun i => ?_)
    simp only [hg]
    have : max (i + (N0 + 1)) N0 = N0 + (i + 1) := by omega
    rw [this]
    push_cast
    congr 1
  set K : ℝ := max C 0 with hK
  have hA : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ K * n := fun n =>
    (hC n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg n))
  have hK0 : 0 ≤ K := le_max_right _ _
  have hs : Summable fun n => ‖f n‖ * g n := by
    apply summable_of_sum_range_le (c := K * ∑' n, g n)
    · intro n; exact mul_nonneg (norm_nonneg _) (hg0 n)
    · intro N
      refine (PNAux.abel_sum_le (fun i => ‖f i‖) g K hA hanti hg0 N).trans ?_
      exact mul_le_mul_of_nonneg_left (hgs.sum_le_tsum _ (fun i _ => hg0 i)) hK0
  rw [← summable_nat_add_iff N0]
  rw [← summable_nat_add_iff N0] at hs
  refine hs.congr (fun n => ?_)
  simp only [hg]
  have : max (n + N0) N0 = n + N0 := by omega
  rw [this]

theorem solution
    (hcheby : (∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(f k : ℂ)‖) n ≤ C * n))
    (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by
  have := (PNAux.summable_gg_mul hcheby hx).mul_left C
  refine this.congr (fun n => ?_)
  unfold gg
  ring
