-- Prove2me | solution 1 for exists_tendsto_rpow_inv_of_le_mul_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:07.189349+00:00
-- url     : https://prove2.me/submissions/54800818-6d68-4432-a085-5117b587a50e

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_BoundedDefect
public import Theorems.Thm_exists_tendsto_div_of_le_add_const
section
@[expose] public section
open Filter
open scoped Topology
private theorem bddBelow_div_of_mul_le {u : ℕ → ℝ} {b : ℝ} (h : ∀ n, 0 < n → n * b ≤ u n) :
    BddBelow (Set.range fun n : ℕ ↦ u n / n) := by
  refine ⟨min b 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  rw [le_div_iff₀ (Nat.cast_pos.2 hn)]
  linarith [h n hn, mul_le_mul_of_nonneg_right (min_le_left b 0) (Nat.cast_nonneg n)]
end
end

set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology
theorem _root_.solution {a : ℕ → ℝ} {K : ℝ} (ha : ∀ n, n ≠ 0 → 0 < a n)
    (hK : 0 < K) (h : ∀ m n, a (m + n) ≤ K * a m * a n) (hc : ∃ c > 0, ∀ n : ℕ, c ^ n ≤ a n) :
    ∃ L > 0, Tendsto (fun n ↦ a n ^ (n : ℝ)⁻¹) atTop (𝓝 L) ∧ ∀ n : ℕ, L ^ n ≤ K * a n := by
  have ha : ∀ n, 0 < a n := by
    have ha1 := ha 1 one_ne_zero
    have ha0 : 0 < a 0 := by
      by_contra! h0
      have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hK.le h0) ha1.le
      linarith [zero_add 1 ▸ h 0 1]
    exact fun n ↦ (eq_or_ne n 0).elim (· ▸ ha0) (ha n)
  have hlog : ∀ m n, Real.log (a (m + n)) ≤ Real.log (a m) + Real.log (a n) + Real.log K :=
    fun m n ↦ by
      have := Real.log_le_log (ha _) (h m n)
      rwa [Real.log_mul (mul_pos hK (ha m)).ne' (ha n).ne', Real.log_mul hK.ne' (ha m).ne',
        add_comm (Real.log K), add_right_comm] at this
  obtain ⟨c, hc0, hcn⟩ := hc
  obtain ⟨ℓ, hℓ, hℓa⟩ := exists_tendsto_div_of_le_add_const hlog <|
    bddBelow_div_of_mul_le fun n _ ↦ by
      simpa [Real.log_pow] using Real.log_le_log (pow_pos hc0 n) (hcn n)
  refine ⟨Real.exp ℓ, Real.exp_pos ℓ, ((Real.continuous_exp.tendsto _).comp hℓ).congr
    fun n ↦ ?_, fun n ↦ ?_⟩
  · simp [Real.rpow_def_of_pos (ha n), div_eq_mul_inv]
  · rw [← Real.exp_nat_mul, ← Real.exp_log (mul_pos hK (ha n)), Real.log_mul hK.ne' (ha n).ne']
    exact Real.exp_le_exp.2 (by linarith [hℓa n])
