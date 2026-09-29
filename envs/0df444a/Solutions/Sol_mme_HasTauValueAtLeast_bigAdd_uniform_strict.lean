-- Prove2me | solution 1 for mme_HasTauValueAtLeast_bigAdd_uniform_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:34:45.890636+00:00
-- url     : https://prove2.me/submissions/11c58bf3-60dd-4c5d-8972-f730be0aac2d

import Mathlib.Tactic
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
import Theorems.Thm_mme_finite_HasTauValueAtLeast_common_multiple_below
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
import Theorems.Thm_mme_balanced_bigAdd_power_type_restrict
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_bigAdd_fin_mul_isomorphic_nested
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem uniform_entropyBits
    (k : ℕ) (hk : 0 < k) :
    mme_modern_entropyBits (fun _ : Fin k => (1 : ℝ) / (k : ℝ)) =
      Real.log (k : ℝ) / Real.log 2 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold mme_modern_entropyBits
  simp only [Real.negMulLog_def, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hkR, Real.log_one]
  field_simp
  ring

private theorem prescribed_fiber_nat_card
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (counts : ι → ℕ)
    (hsum : ∑ i, counts i = Fintype.card α) :
    Nat.card
        {g : α → ι // ∀ i,
          Fintype.card {a // g a = i} = counts i} =
      (Fintype.card α).factorial / ∏ i, (counts i).factorial := by
  rw [Nat.card_eq_fintype_card]
  exact mme_fintype_prescribed_fiber_function_card counts hsum

private theorem uniform_balanced_word_card
    (k m : ℕ) :
    Nat.card
        {w : Fin (k * m) → Fin k // ∀ p,
          Fintype.card {j // w j = p} = m} =
      Nat.multinomial Finset.univ (fun _ : Fin k => m) := by
  have hsum : ∑ _ : Fin k, m = Fintype.card (Fin (k * m)) := by
    simp [Finset.sum_const, Fintype.card_fin]
  have hcard :=
    prescribed_fiber_nat_card
      (α := Fin (k * m)) (ι := Fin k) (fun _ => m) hsum
  calc
    Nat.card
        {w : Fin (k * m) → Fin k // ∀ p,
          Fintype.card {j // w j = p} = m} =
        (Fintype.card (Fin (k * m))).factorial /
          ∏ _ : Fin k, m.factorial := hcard
    _ = Nat.multinomial Finset.univ (fun _ : Fin k => m) := by
      rw [Nat.multinomial]
      simp only [Fintype.card_fin, Finset.sum_const, Finset.card_fin]
      congr 2

private theorem uniform_multinomial_sqrt_lower
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    ((k : ℝ) ^ (k * m)) *
        Real.exp (-(6 * (k : ℝ)) *
          Real.sqrt ((((k * m) + 1 : ℕ) : ℝ))) ≤
      (Nat.multinomial Finset.univ (fun _ : Fin k => m) : ℝ) := by
  let N : ℕ := k * m
  let s : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let D : ℝ := (6 * (((N + 1 : ℕ) : ℝ)) : ℝ) ^ k
  have hsum : ∑ _ : Fin k, (1 : ℕ) = k := by simp
  have hentropy :=
    mme_dwz_multinomial_entropy_polynomial_lower
      (fun _ : Fin k => (1 : ℕ)) m hm (by simpa using hk)
  have hleft :
      Real.exp
          ((m : ℝ) * ((k : ℝ) * Real.log 2 *
            mme_modern_entropyBits
              (fun _ : Fin k => (1 : ℝ) / (k : ℝ)))) =
        (k : ℝ) ^ N := by
    rw [uniform_entropyBits k hk]
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    rw [show (k : ℝ) * Real.log 2 *
          (Real.log (k : ℝ) / Real.log 2) =
          (k : ℝ) * Real.log (k : ℝ) by field_simp]
    rw [show (m : ℝ) * ((k : ℝ) * Real.log (k : ℝ)) =
          (N : ℝ) * Real.log (k : ℝ) by
            dsimp [N]
            push_cast
            ring]
    rw [← Real.log_pow]
    exact Real.exp_log (pow_pos hkR N)
  have hentropy' :
      (k : ℝ) ^ N ≤ D *
        (Nat.multinomial Finset.univ (fun _ : Fin k => m) : ℝ) := by
    rw [← hleft]
    simpa only [hsum, one_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, Nat.cast_mul, Fintype.card_fin, D, N] using hentropy
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : 1 ≤ s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by norm_num]
    apply Real.sqrt_le_sqrt
    norm_num
  have hs_sq : s ^ 2 = (((N + 1 : ℕ) : ℝ)) := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have hbase : 6 * (((N + 1 : ℕ) : ℝ)) ≤ Real.exp (6 * s) := by
    have hs_le : s ≤ s + 1 := by linarith
    have htwo : (2 : ℝ) ≤ s + 1 := by linarith
    have hs2_le : s ^ 2 ≤ (s + 1) ^ 2 := by gcongr
    have hsix_le : (6 : ℝ) ≤ (s + 1) ^ 4 := by
      calc
        (6 : ℝ) ≤ 2 ^ 4 := by norm_num
        _ ≤ (s + 1) ^ 4 := by gcongr
    have hpoly : 6 * s ^ 2 ≤ (s + 1) ^ 6 := by
      calc
        6 * s ^ 2 ≤ (s + 1) ^ 4 * (s + 1) ^ 2 :=
          mul_le_mul hsix_le hs2_le (sq_nonneg _) (by positivity)
        _ = (s + 1) ^ 6 := by ring
    have hexp : (s + 1) ^ 6 ≤ (Real.exp s) ^ 6 := by
      gcongr
      exact Real.add_one_le_exp s
    calc
      6 * (((N + 1 : ℕ) : ℝ)) = 6 * s ^ 2 := by rw [hs_sq]
      _ ≤ (s + 1) ^ 6 := hpoly
      _ ≤ (Real.exp s) ^ 6 := hexp
      _ = Real.exp (6 * s) := by rw [← Real.exp_nat_mul]; norm_num
  have hD : D ≤ Real.exp ((6 * (k : ℝ)) * s) := by
    dsimp [D]
    calc
      (6 * (((N + 1 : ℕ) : ℝ))) ^ k ≤
          (Real.exp (6 * s)) ^ k := by gcongr
      _ = Real.exp ((6 * (k : ℝ)) * s) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hcancel :
      D * Real.exp (-(6 * (k : ℝ)) * s) ≤ 1 := by
    calc
      D * Real.exp (-(6 * (k : ℝ)) * s) ≤
          Real.exp ((6 * (k : ℝ)) * s) *
            Real.exp (-(6 * (k : ℝ)) * s) := by
              gcongr
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  calc
    (k : ℝ) ^ (k * m) *
          Real.exp (-(6 * (k : ℝ)) *
            Real.sqrt ((((k * m) + 1 : ℕ) : ℝ))) =
        (k : ℝ) ^ N * Real.exp (-(6 * (k : ℝ)) * s) := by rfl
    _ ≤ (D * (Nat.multinomial Finset.univ
          (fun _ : Fin k => m) : ℝ)) *
        Real.exp (-(6 * (k : ℝ)) * s) := by
          gcongr
    _ = (Nat.multinomial Finset.univ (fun _ : Fin k => m) : ℝ) *
        (D * Real.exp (-(6 * (k : ℝ)) * s)) := by ring
    _ ≤ (Nat.multinomial Finset.univ (fun _ : Fin k => m) : ℝ) * 1 := by
      gcongr
    _ = (Nat.multinomial Finset.univ (fun _ : Fin k => m) : ℝ) := by ring

private theorem balanced_bigAdd_finite_extraction
    {K : Type u} [Field K] {k : ℕ}
    (F : Fin k → TensorObj K 3) (hk : 0 < k)
    (tau W : ℝ) (hW : 0 ≤ W)
    (E : ℕ) (hE : 0 < E)
    (hcommon : ∀ (r : ℕ) (i : Fin k),
      ∃ (q : ℕ) (a b c : Fin q → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
          ((F i).kronPow (r * E)) ∧
        W ^ (r * E) ≤
          ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau))
    (r : ℕ) (hr : 0 < r) :
    ∃ (q : ℕ) (A B C : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (C j)))
        ((TensorObj.bigAdd F).kronPow (k * (r * E))) ∧
      (((k : ℝ) * W) ^ (k * (r * E))) *
          Real.exp (-(6 * (k : ℝ)) *
            Real.sqrt ((((k * (r * E)) + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by
  classical
  let m : ℕ := r * E
  let N : ℕ := k * m
  let Count : ℕ :=
    Nat.card
      {w : Fin N → Fin k // ∀ p,
        Fintype.card {j // w j = p} = m}
  have hm : 0 < m := Nat.mul_pos hr hE
  have hlocal : ∀ i : Fin k,
      ∃ (q : ℕ) (a b c : Fin q → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
          ((F i).kronPow m) ∧
        W ^ m ≤
          ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    intro i
    simpa only [m] using hcommon r i
  obtain ⟨q, a, b, c, hproductRestrict, hproductWeight⟩ :=
    mme_finite_MM_extractions_kronFin_tau_product
      (K := K) (fun i : Fin k ↦ (F i).kronPow m) tau
      (fun _ : Fin k ↦ W ^ m)
      (fun _ ↦ pow_nonneg hW m) hlocal
  have hproductWeight' :
      W ^ N ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    calc
      W ^ N = ∏ _ : Fin k, W ^ m := by
        simp only [Finset.prod_const, Finset.card_fin, N]
        rw [← pow_mul]
        congr 1
        exact Nat.mul_comm k m
      _ ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := hproductWeight
  have hreplicate :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin Count ↦
          TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j))))
        (TensorObj.bigAdd (fun _ : Fin Count ↦
          TensorObj.kronFin k (fun i ↦ (F i).kronPow m))) :=
    mme_bigAdd_mono_restrict (fun _ ↦ hproductRestrict)
  have hbalanced :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin Count ↦
          TensorObj.kronFin k (fun i ↦ (F i).kronPow m)))
        ((TensorObj.bigAdd F).kronPow N) := by
    simpa only [N, Count] using
      (mme_balanced_bigAdd_power_type_restrict (K := K) F hk (r := m))
  let A : Fin (Count * q) → ℕ := fun j ↦ a (finProdFinEquiv.symm j).2
  let B : Fin (Count * q) → ℕ := fun j ↦ b (finProdFinEquiv.symm j).2
  let C : Fin (Count * q) → ℕ := fun j ↦ c (finProdFinEquiv.symm j).2
  refine ⟨Count * q, A, B, C, ?_, ?_⟩
  · have hflat :
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j : Fin (Count * q) ↦
            MMObj K (A j) (B j) (C j)))
          (TensorObj.bigAdd (fun _ : Fin Count ↦
            TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))) := by
      simpa only [A, B, C] using
        (mme_bigAdd_fin_mul_isomorphic_nested
          (K := K)
          (fun _ : Fin Count ↦
            fun j : Fin q ↦ MMObj K (a j) (b j) (c j))).1
    simpa only [N] using
      TensorObj.Restrict.trans hflat
        (TensorObj.Restrict.trans hreplicate hbalanced)
  · have hCount :
        ((k : ℝ) ^ N) *
            Real.exp (-(6 * (k : ℝ)) *
              Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          (Count : ℝ) := by
      have hmulti := uniform_multinomial_sqrt_lower k m hk hm
      rw [← uniform_balanced_word_card k m] at hmulti
      simpa only [N, Count] using hmulti
    have hrate :
        (((k : ℝ) * W) ^ N) *
            Real.exp (-(6 * (k : ℝ)) *
              Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          (Count : ℝ) * W ^ N := by
      calc
        (((k : ℝ) * W) ^ N) *
              Real.exp (-(6 * (k : ℝ)) *
                Real.sqrt (((N + 1 : ℕ) : ℝ))) =
            (((k : ℝ) ^ N) *
              Real.exp (-(6 * (k : ℝ)) *
                Real.sqrt (((N + 1 : ℕ) : ℝ)))) * W ^ N := by
                  rw [mul_pow]
                  ring
        _ ≤ (Count : ℝ) * W ^ N := by
          gcongr
    have hsum :
        (Count : ℝ) *
            (∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) =
          ∑ j : Fin (Count * q),
            (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by
      calc
        (Count : ℝ) *
              (∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) =
            ∑ p : Fin Count × Fin q,
              (((a p.2 * b p.2 * c p.2 : ℕ) : ℝ) ^ tau) := by
                rw [Fintype.sum_prod_type]
                simp only [Finset.sum_const, Finset.card_fin]
                rw [nsmul_eq_mul', mul_comm]
        _ = ∑ j : Fin (Count * q),
              (((A j * B j * C j : ℕ) : ℝ) ^ tau) := by
          simpa only [A, B, C] using
            (Equiv.sum_comp finProdFinEquiv.symm
              (fun p : Fin Count × Fin q ↦
                (((a p.2 * b p.2 * c p.2 : ℕ) : ℝ) ^ tau))).symm
    change
      (((k : ℝ) * W) ^ N) *
          Real.exp (-(6 * (k : ℝ)) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        ∑ j : Fin (Count * q),
          (((A j * B j * C j : ℕ) : ℝ) ^ tau)
    calc
      (((k : ℝ) * W) ^ N) *
            Real.exp (-(6 * (k : ℝ)) *
              Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          (Count : ℝ) * W ^ N := hrate
      _ ≤ (Count : ℝ) *
          (∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) := by
            gcongr
      _ = ∑ j : Fin (Count * q),
          (((A j * B j * C j : ℕ) : ℝ) ^ tau) := hsum

theorem solution
    {K : Type u} [Field K] {k : ℕ}
    (F : Fin k → TensorObj K 3)
    (tau B : ℝ) (hB : 0 ≤ B)
    (hcomponent : ∀ i : Fin k, ∀ W : ℝ,
      0 ≤ W → W < B → HasTauValueAtLeast (F i) tau W)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < (k : ℝ) * B) :
    HasTauValueAtLeast (TensorObj.bigAdd F) tau V := by
  have hk : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    norm_num at hVlt
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hBpos : 0 < B := by
    by_contra hB0
    have : B = 0 := le_antisymm (le_of_not_gt hB0) hB
    rw [this, mul_zero] at hVlt
    linarith
  let W : ℝ := (V / (k : ℝ) + B) / 2
  have hVkB : V / (k : ℝ) < B := by
    rw [div_lt_iff₀ hkR]
    simpa only [mul_comm] using hVlt
  have hWpos : 0 < W := by
    dsimp [W]
    have : 0 ≤ V / (k : ℝ) := div_nonneg hV (le_of_lt hkR)
    linarith
  have hW : 0 ≤ W := le_of_lt hWpos
  have hWltB : W < B := by
    dsimp [W]
    linarith
  have hVltRate : V < (k : ℝ) * W := by
    have hVW : V / (k : ℝ) < W := by
      dsimp [W]
      linarith
    rw [div_lt_iff₀ hkR] at hVW
    simpa only [mul_comm] using hVW
  let base : ℝ := (W + B) / 2
  have hbasePos : 0 < base := by
    dsimp [base]
    linarith
  have hbaseLt : base < B := by
    dsimp [base]
    linarith
  have hWbase : W < base := by
    dsimp [base]
    linarith
  have hvalues : ∀ i : Fin k,
      HasTauValueAtLeast (F i) tau base := by
    intro i
    exact hcomponent i base (le_of_lt hbasePos) hbaseLt
  obtain ⟨E, hE, hcommon⟩ :=
    mme_finite_HasTauValueAtLeast_common_multiple_below
      F tau (fun _ : Fin k ↦ base) (fun _ : Fin k ↦ W)
      (fun _ ↦ hbasePos) (fun _ ↦ hW) (fun _ ↦ hWbase) hvalues
  let scale : ℕ → ℕ := fun r ↦ k * (r * E)
  have hscale : Tendsto scale atTop atTop := by
    rw [tendsto_atTop]
    intro n
    filter_upwards [eventually_ge_atTop n] with r hr
    dsimp [scale]
    have hk1 : 1 ≤ k := hk
    have hE1 : 1 ≤ E := hE
    have hrE : r ≤ r * E := by
      simpa only [mul_one] using Nat.mul_le_mul_left r hE1
    calc
      n ≤ r := hr
      _ = 1 * r := by simp
      _ ≤ k * (r * E) := Nat.mul_le_mul hk1 hrE
  let C : ℝ := 6 * (k : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hRate : 0 ≤ (k : ℝ) * W := mul_nonneg (le_of_lt hkR) hW
  have habsorb :=
    mme_strict_pow_absorbs_sqrt_exp_loss
      V ((k : ℝ) * W) C hV hVltRate hC
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (TensorObj.bigAdd F) tau V hV scale hscale (fun _ : ℕ ↦ (0 : ℝ))
      tendsto_const_nhds
  filter_upwards [hscale.eventually habsorb, eventually_ge_atTop 1] with r hrBound hr
  obtain ⟨q, A, Bdim, Cdim, hrestrict, hweight⟩ :=
    balanced_bigAdd_finite_extraction F hk tau W hW E hE hcommon r (by omega)
  refine ⟨q, A, Bdim, Cdim, hrestrict, ?_⟩
  calc
    V ^ (scale r) * (1 - (0 : ℝ)) = V ^ (scale r) := by ring
    _ ≤ (((k : ℝ) * W) ^ (scale r)) *
        Real.exp (-C * Real.sqrt ((((scale r) + 1 : ℕ) : ℝ))) := hrBound
    _ ≤ ∑ j, (((A j * Bdim j * Cdim j : ℕ) : ℝ) ^ tau) := by
      simpa only [scale, C] using hweight
