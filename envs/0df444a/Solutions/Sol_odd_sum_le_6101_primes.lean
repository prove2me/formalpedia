-- Prove2me | solution 1 for odd_sum_le_6101_primes
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T05:18:13.401104+00:00
-- url     : https://prove2.me/submissions/dfb232e4-7114-4507-ab43-3d92384fe5ba

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_Schnir_pi_lower
import Theorems.Thm_Schnir_pointwise_bound
import Theorems.Thm_Schnir_C_mean
import Theorems.Thm_Schnir_schnirelmann_ineq

/-!
Every odd `n > 1` is a sum of at most `6101` primes.

Same route as the proved `100001` / `97041` entries, with a sharper density input
`σ(A) ≥ 1/2200` (weighted second moment):
* part a: triangle first moment `∑_{s ≤ n} r(s) ≥ 2 (n-1000)(n-3001) / (9 log² n)`;
* part b: summation by parts and the per-term bound for the weight `log² s / s`;
* part c: `W(n) = ∑_{e^1000 < s ≤ n} r(s) log² s / s ≥ 0.443 n`, then weighted
  Cauchy–Schwarz with `pointwise_bound` and `C_mean` gives `R(n) ≥ n / 4340` for `n ≥ e^2000`;
* part d: `σ(A) ≥ 1/2200`, Schnirelmann iteration with `m = 1525`, and `K = 4m + 1 = 6101`.
-/

open Finset Real

namespace Schnir

-- ===== part a =====

/-- odd primes `≤ t`. -/
def s6P (t : ℕ) : Finset ℕ := (range (t + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

lemma s6_card_P (M : ℕ) (hM : 2 ≤ M) : (s6P M).card + 1 = Nat.primeCounting M := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have : s6P M = ((Finset.range (M + 1)).filter Nat.Prime).erase 2 := by
    ext p; simp [s6P, Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_add_one]
  simp [Nat.prime_two]; omega

lemma s6_Q_lower (n t : ℕ) (hn : 1000 ≤ n) (ht : t ≤ n) :
    2 / (3 * Real.log n) * ((t : ℝ) - 1000) ≤ (s6P t).card := by
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  by_cases h : t < 1000
  · have : ((t : ℝ) - 1000) ≤ 0 := by
      have : (t : ℝ) < 1000 := by exact_mod_cast h
      linarith
    have : 2 / (3 * Real.log n) * ((t : ℝ) - 1000) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    exact this.trans (Nat.cast_nonneg _)
  · push Not at h
    have ht' : (1000 : ℝ) ≤ t := by exact_mod_cast h
    have hp := pi_lower t ht'
    rw [Nat.floor_natCast] at hp
    have hc := s6_card_P t (by omega)
    have hc' : ((s6P t).card : ℝ) = (Nat.primeCounting t : ℝ) - 1 := by
      rw [← hc]; push_cast; ring
    rw [hc']
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hle : Real.log t ≤ Real.log n := Real.log_le_log (by linarith) (by exact_mod_cast ht)
    have h1 : 2 / (3 * Real.log n) * ((t : ℝ) - 1000) ≤ 2 * t / (3 * Real.log n) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have h2 : 2 * (t : ℝ) / (3 * Real.log n) ≤ 2 * t / (3 * Real.log t) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    linarith

/-- `∑_{s ≤ n} r s ≥ ∑_{p ∈ P(K)} Q(n - p)` for `K ≤ n`. -/
lemma s6_pairs (n K : ℕ) (hK : K ≤ n) :
    ∑ p ∈ s6P K, (s6P (n - p)).card ≤ ∑ s ∈ range (n + 1), r s := by
  unfold r
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun pq => (⟨pq.1 + pq.2, pq.1⟩ : Σ _ : ℕ, ℕ))
  · intro pq hpq
    simp only [Finset.mem_coe, Finset.mem_sigma, s6P, Finset.mem_filter, Finset.mem_range] at hpq ⊢
    obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩ := hpq
    refine ⟨by omega, by omega, h2, h3, ?_, ?_⟩
    · rw [Nat.add_sub_cancel_left]; exact h5
    · rw [Nat.add_sub_cancel_left]; exact h6
  · intro a _ b _ hab
    simp only [Sigma.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have h2' : a.1 = b.1 := eq_of_heq h2
    exact Sigma.ext h2' (heq_of_eq (by omega))

lemma s6_Ico_card (p K : ℕ) : ((range K).filter (fun t => p ≤ t)).card = K - p := by
  have : (range K).filter (fun t => p ≤ t) = Ico p K := by
    ext t; simp [Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]

/-- `∑_{p ∈ P(K)} (K - p) = ∑_{t < K} Q(t)`. -/
lemma s6_swap (K : ℕ) : ∑ p ∈ s6P K, (K - p) = ∑ t ∈ range K, (s6P t).card := by
  have h1 : ∀ p ∈ s6P K, K - p = ∑ t ∈ range K, if p ≤ t then 1 else 0 := by
    intro p _
    rw [Finset.sum_boole, ← s6_Ico_card p K]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_boole]
  simp only [Nat.cast_id]
  congr 1
  ext p
  simp only [s6P, Finset.mem_filter, Finset.mem_range] at ht ⊢
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, by omega⟩

lemma s6_gauss (K : ℕ) : ∑ t ∈ range K, ((t : ℝ) - 1000) = (K : ℝ) * (K - 1) / 2 - 1000 * K := by
  induction K with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The lower function `L(t) = 2 (t - 1000)(t - 3001) / (9 (log t)^2)`. -/
noncomputable def s6L (t : ℝ) : ℝ := 2 * (t - 1000) * (t - 3001) / (9 * (Real.log t) ^ 2)

/-- Triangle first moment: `∑_{s ≤ n} r(s) ≥ L(n)` for `n ≥ 1000`. -/
theorem s6_first_moment (n : ℕ) (hn : 1000 ≤ n) :
    s6L n ≤ ∑ s ∈ range (n + 1), (r s : ℝ) := by
  set K := n - 1000 with hKdef
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  set c := 2 / (3 * Real.log n) with hc
  have hc0 : 0 ≤ c := by positivity
  have hK : (K : ℝ) = n - 1000 := by rw [hKdef]; push_cast [hn]; ring
  -- step 1
  have hstep1 : ∑ p ∈ s6P K, ((s6P (n - p)).card : ℝ) ≤ ∑ s ∈ range (n + 1), (r s : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]; exact_mod_cast s6_pairs n K (by omega)
  -- step 2
  have hstep2 : c * ∑ p ∈ s6P K, ((K - p : ℕ) : ℝ) ≤ ∑ p ∈ s6P K, ((s6P (n - p)).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simp only [s6P, Finset.mem_filter, Finset.mem_range] at hp
    have := s6_Q_lower n (n - p) hn (by omega)
    have e : ((n - p : ℕ) : ℝ) - 1000 = ((K - p : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hK]; ring
    rw [e] at this; exact this
  -- step 3
  have hstep3 : ∑ p ∈ s6P K, ((K - p : ℕ) : ℝ) = ∑ t ∈ range K, ((s6P t).card : ℝ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum, s6_swap]
  -- step 4
  have hstep4 : c * ∑ t ∈ range K, ((t : ℝ) - 1000) ≤ ∑ t ∈ range K, ((s6P t).card : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    simp only [Finset.mem_range] at ht
    exact s6_Q_lower n t hn (by omega)
  rw [s6_gauss] at hstep4
  have hfin : s6L n = c * (c * ((K : ℝ) * (K - 1) / 2 - 1000 * K)) := by
    rw [s6L, hc, hK]; field_simp; ring
  rw [hfin]
  calc c * (c * ((K : ℝ) * (K - 1) / 2 - 1000 * K))
      ≤ c * ∑ t ∈ range K, ((s6P t).card : ℝ) := mul_le_mul_of_nonneg_left hstep4 hc0
    _ = c * ∑ p ∈ s6P K, ((K - p : ℕ) : ℝ) := by rw [hstep3]
    _ ≤ _ := hstep2.trans hstep1


-- ===== part b =====

/-- Summation by parts, as an inequality. -/
lemma s6_abel (a w L : ℕ → ℝ) (n0 : ℕ)
    (hw : ∀ k, n0 < k → w (k + 1) ≤ w k)
    (hML : ∀ k, n0 < k → L k ≤ ∑ s ∈ range (k + 1), a s) :
    ∀ n, n0 ≤ n →
      ∑ s ∈ Ioc n0 n, (L s - L (s - 1)) * w s
        + (∑ s ∈ range (n + 1), a s - L n) * w (n + 1)
        - (∑ s ∈ range (n0 + 1), a s - L n0) * w (n0 + 1)
      ≤ ∑ s ∈ Ioc n0 n, a s * w s := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ioc_succ_top hk, Finset.sum_Ioc_succ_top hk, Finset.sum_range_succ _ (k + 1)]
    have h1 := hML (k + 1) (by omega)
    have h2 := hw (k + 1) (by omega)
    rw [Finset.sum_range_succ] at h1
    simp only [Nat.add_sub_cancel] at ih ⊢
    have h3 : 0 ≤ (∑ s ∈ range (k + 1), a s + a (k + 1) - L (k + 1)) * (w (k + 1) - w (k + 1 + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- Per-term bound: `(L(t) - L(t-1)) · (log t)^2 / t ≥ 0.4439` for `t ≥ e^1000`. -/
lemma s6_term (t : ℝ) (ht : Real.exp 1000 ≤ t) :
    4439 / 10000 ≤ (s6L t - s6L (t - 1)) * (Real.log t ^ 2 / t) := by
  have hbig : (10 : ℝ) ^ 9 ≤ t := by
    have h1 : (251 : ℝ) ≤ Real.exp 250 := by have := Real.add_one_le_exp (250 : ℝ); linarith
    have h2 : Real.exp 1000 = Real.exp 250 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (251 : ℝ) ^ 4 ≤ Real.exp 250 ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
    nlinarith
  have ht1 : (0 : ℝ) < t - 1 := by linarith
  set u := Real.log t with hu_def
  set v := Real.log (t - 1) with hv_def
  have hu : 1000 ≤ u := by
    have := Real.log_le_log (Real.exp_pos 1000) ht
    rwa [Real.log_exp] at this
  have hvu : v ≤ u := Real.log_le_log ht1 (by linarith)
  have huv : u - v ≤ 1 / (t - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < t / (t - 1) by positivity)
    rw [Real.log_div (by linarith) ht1.ne'] at h
    have : t / (t - 1) - 1 = 1 / (t - 1) := by field_simp; ring
    linarith
  have hinv : 1 / (t - 1) ≤ 1 / 1000 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hv : 999 ≤ v := by linarith
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := by linarith
  -- u^2 - v^2 ≤ 2u/(t-1)
  have hsq : u ^ 2 - v ^ 2 ≤ 2 * u / (t - 1) := by
    have : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
    rw [this]
    calc (u - v) * (u + v) ≤ 1 / (t - 1) * (u + v) :=
          mul_le_mul_of_nonneg_right huv (by linarith)
      _ ≤ 1 / (t - 1) * (2 * u) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * u / (t - 1) := by ring
  -- u / v^2 ≤ 1/990
  have huv2 : u / v ^ 2 ≤ 1 / 990 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- u^2 / v^2 ≤ 1 + (2/990)/(t-1)
  have hratio : u ^ 2 / v ^ 2 ≤ 1 + 2 / 990 / (t - 1) := by
    have e : u ^ 2 / v ^ 2 = 1 + (u ^ 2 - v ^ 2) / v ^ 2 := by field_simp; ring
    rw [e]
    have : (u ^ 2 - v ^ 2) / v ^ 2 ≤ 2 * u / (t - 1) / v ^ 2 :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have e2 : 2 * u / (t - 1) / v ^ 2 = 2 * (u / v ^ 2) / (t - 1) := by field_simp
    have : 2 * (u / v ^ 2) / (t - 1) ≤ 2 * (1 / 990) / (t - 1) :=
      div_le_div_of_nonneg_right (by linarith) ht1.le
    have e3 : 2 * (1 / 990) / (t - 1) = 2 / 990 / (t - 1) := by ring
    linarith
  -- f(t-1) bounds
  set g := (t - 1 - 1000) * (t - 1 - 3001) with hg
  have hg0 : 0 ≤ g := by rw [hg]; apply mul_nonneg <;> linarith
  have hgle : g ≤ (t - 1) ^ 2 := by rw [hg]; nlinarith
  have hexp : (s6L t - s6L (t - 1)) * (u ^ 2 / t)
      = 2 / 9 * ((t - 1000) * (t - 3001) - g * (u ^ 2 / v ^ 2)) / t := by
    rw [s6L, s6L, ← hu_def, ← hv_def, hg]
    field_simp
  rw [hexp]
  have hgr : g * (u ^ 2 / v ^ 2) ≤ g + 2 / 990 * (t - 1) := by
    calc g * (u ^ 2 / v ^ 2) ≤ g * (1 + 2 / 990 / (t - 1)) := mul_le_mul_of_nonneg_left hratio hg0
      _ = g + 2 / 990 * (g / (t - 1)) := by ring
      _ ≤ g + 2 / 990 * (t - 1) := by
        have : g / (t - 1) ≤ t - 1 := by
          rw [div_le_iff₀ ht1]; nlinarith
        linarith
  rw [le_div_iff₀ (by linarith)]
  have e4 : (t - 1000) * (t - 3001) = g + 2 * t - 4002 := by rw [hg]; ring
  rw [e4]
  nlinarith


-- ===== part c =====

theorem s6_r_le (s : ℕ) : r s ≤ s := by
  unfold r
  calc _ ≤ (Finset.Icc 1 s).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp
        have := hp.2.1.one_lt
        simp only [Finset.mem_Icc]; omega
    _ = s := by simp

theorem s6_r_odd (s : ℕ) (hs : ¬ Even s) : r s = 0 := by
  unfold r
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp ⟨hpp, hp2, hqp, hq2⟩
  simp only [Finset.mem_range] at hp
  have h1 := hpp.odd_of_ne_two hp2
  have h2 := hqp.odd_of_ne_two hq2
  have : Even (p + (s - p)) := Odd.add_odd h1 h2
  rw [Nat.add_sub_cancel' (by omega)] at this
  exact hs this

theorem s6_mono (a b : ℝ) (ha : 1000 ≤ a) (hab : a ≤ b) :
    Real.exp a / a ^ 2 ≤ Real.exp b / b ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : b ≤ a * (1 + (b - a) / 2) := by nlinarith
  have h2 : 1 + (b - a) / 2 ≤ Real.exp ((b - a) / 2) := by
    have := Real.add_one_le_exp ((b - a) / 2); linarith
  have h3 : b ≤ a * Real.exp ((b - a) / 2) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 ha0.le)
  have h4 : b ^ 2 ≤ a ^ 2 * Real.exp (b - a) := by
    have : Real.exp (b - a) = Real.exp ((b - a) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [this, ← mul_pow]
    exact pow_le_pow_left₀ hb0.le h3 2
  have h5 : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h5]
  have := Real.exp_pos a
  nlinarith

/-- The weight `(log t)^2 / t` decreases past `e^1000`. -/
theorem s6_w_anti (k : ℝ) (hk : Real.exp 1000 ≤ k) :
    Real.log (k + 1) ^ 2 / (k + 1) ≤ Real.log k ^ 2 / k := by
  have hk0 : 0 < k := lt_of_lt_of_le (Real.exp_pos _) hk
  have hu : 1000 ≤ Real.log k := by
    have := Real.log_le_log (Real.exp_pos 1000) hk
    rwa [Real.log_exp] at this
  have huv : Real.log k ≤ Real.log (k + 1) := Real.log_le_log hk0 (by linarith)
  have h := s6_mono _ _ hu huv
  rw [Real.exp_log hk0, Real.exp_log (by linarith)] at h
  have hv : 0 < Real.log (k + 1) := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h ⊢
  linarith

theorem s6_exp1000 : (10 : ℝ) ^ 20 ≤ Real.exp 1000 := by
  have h1 : (101 : ℝ) ≤ Real.exp 100 := by have := Real.add_one_le_exp (100 : ℝ); linarith
  have h2 : Real.exp 1000 = Real.exp 100 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : (101 : ℝ) ^ 10 ≤ Real.exp 100 ^ 10 := pow_le_pow_left₀ (by norm_num) h1 10
  have h4 : (10 : ℝ) ^ 20 ≤ 101 ^ 10 := by norm_num
  linarith

/-- Weighted first moment: `W(n) ≥ 0.443 n` for `n ≥ e^2000`. -/
theorem s6_W (n : ℕ) (hn : Real.exp 2000 ≤ n) :
    443 / 1000 * (n : ℝ) ≤ ∑ s ∈ Ioc ⌊Real.exp 1000⌋₊ n, (r s : ℝ) * (Real.log s ^ 2 / s) := by
  set n0 := ⌊Real.exp 1000⌋₊ with hn0def
  have hE := s6_exp1000
  have hn0 : (n0 : ℝ) ≤ Real.exp 1000 := Nat.floor_le (Real.exp_pos _).le
  have hn0' : Real.exp 1000 < n0 + 1 := Nat.lt_floor_add_one _
  have hexp2 : Real.exp 2000 = Real.exp 1000 * Real.exp 1000 := by
    rw [← Real.exp_add]; norm_num
  have hnn0 : n0 ≤ n := by
    have : (n0 : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hbig : ∀ k : ℕ, n0 < k → Real.exp 1000 ≤ k := by
    intro k hk
    have : (n0 : ℝ) + 1 ≤ k := by exact_mod_cast hk
    linarith
  have habel := s6_abel (fun s => (r s : ℝ)) (fun s => Real.log s ^ 2 / s) (fun s => s6L s) n0
    (by
      intro k hk
      have := s6_w_anti k (hbig k hk)
      push_cast; exact this)
    (by
      intro k hk
      have h1 := hbig k hk
      have : (1000 : ℝ) ≤ k := by nlinarith
      exact s6_first_moment k (by exact_mod_cast this))
    n hnn0
  -- (i) main sum
  have hi : 4439 / 10000 * ((n : ℝ) - n0) ≤
      ∑ s ∈ Ioc n0 n, (s6L s - s6L ((s - 1 : ℕ) : ℝ)) * (Real.log s ^ 2 / s) := by
    have hcard : ((Ioc n0 n).card : ℝ) = (n : ℝ) - n0 := by
      rw [Nat.card_Ioc, Nat.cast_sub hnn0]
    rw [← hcard, mul_comm, ← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro s hs
    simp only [Finset.mem_Ioc] at hs
    have h1 := hbig s hs.1
    have : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [this]
    exact s6_term s h1
  -- (ii) the end term is nonnegative
  have hii : 0 ≤ (∑ s ∈ range (n + 1), (r s : ℝ) - s6L n) * (Real.log ((n + 1 : ℕ) : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
    apply mul_nonneg
    · have h1 := hbig n (by
        by_contra h; push Not at h
        have : n = n0 := le_antisymm h hnn0
        rw [this] at hn; nlinarith)
      have : (1000 : ℝ) ≤ n := by nlinarith
      have := s6_first_moment n (by exact_mod_cast this)
      linarith
    · positivity
  -- (iii) the start term is small
  have hiii : (∑ s ∈ range (n0 + 1), (r s : ℝ) - s6L n0) * (Real.log ((n0 + 1 : ℕ) : ℝ) ^ 2 / ((n0 + 1 : ℕ) : ℝ))
      ≤ 2 * 1001 ^ 2 * Real.exp 1000 := by
    have hn0big : (3001 : ℝ) ≤ n0 := by
      have : (3002 : ℝ) ≤ Real.exp 1000 := by nlinarith
      have : (3002 : ℝ) < n0 + 1 := by linarith
      have : (3002 : ℕ) < n0 + 1 := by exact_mod_cast this
      exact_mod_cast (show 3001 ≤ n0 by omega)
    have hL0 : 0 ≤ s6L n0 := by
      unfold s6L
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
    have hM0 : ∑ s ∈ range (n0 + 1), (r s : ℝ) ≤ ((n0 : ℝ) + 1) ^ 2 := by
      have : ∑ s ∈ range (n0 + 1), (r s : ℝ) ≤ (range (n0 + 1)).card • ((n0 : ℝ) + 1) := by
        apply Finset.sum_le_card_nsmul
        intro s hs
        simp only [Finset.mem_range] at hs
        have : r s ≤ n0 + 1 := (s6_r_le s).trans (by omega)
        exact_mod_cast this
      rw [Finset.card_range, nsmul_eq_mul] at this
      push_cast at this; nlinarith
    push_cast
    set m := (n0 : ℝ) + 1 with hm
    have hm0 : 0 < m := by linarith
    have hlogm : Real.log m ≤ 1001 := by
      rw [Real.log_le_iff_le_exp hm0]
      have : Real.exp 1001 = Real.exp 1000 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      nlinarith
    have hlogm0 : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
    have hw0 : 0 ≤ Real.log m ^ 2 / m := by positivity
    calc (∑ s ∈ range (n0 + 1), (r s : ℝ) - s6L n0) * (Real.log m ^ 2 / m)
        ≤ m ^ 2 * (Real.log m ^ 2 / m) := mul_le_mul_of_nonneg_right (by linarith) hw0
      _ = m * Real.log m ^ 2 := by field_simp
      _ ≤ (2 * Real.exp 1000) * 1001 ^ 2 := by
          apply mul_le_mul (by linarith) (pow_le_pow_left₀ hlogm0 hlogm 2) (by positivity) (by positivity)
      _ = 2 * 1001 ^ 2 * Real.exp 1000 := by ring
  have hn1 : (n : ℝ) ≥ 10 ^ 20 * Real.exp 1000 := by nlinarith
  push_cast at hii hiii habel
  nlinarith

/-- Support bound: `R(n) ≥ n / 4340` for `n ≥ e^2000`. -/
theorem s6_R (n : ℕ) (hn : Real.exp 2000 ≤ n) :
    (n : ℝ) / 4340 ≤ (((range (n + 1)).filter (fun s => 0 < r s)).card : ℝ) := by
  set n0 := ⌊Real.exp 1000⌋₊ with hn0def
  have hn0' : Real.exp 1000 < n0 + 1 := Nat.lt_floor_add_one _
  have hbig : ∀ k : ℕ, n0 < k → Real.exp 1000 ≤ k := by
    intro k hk
    have : (n0 : ℝ) + 1 ≤ k := by exact_mod_cast hk
    linarith
  have hW := s6_W n hn
  set F := (Ioc n0 n).filter (fun s => 0 < r s) with hF
  set R := (range (n + 1)).filter (fun s => 0 < r s) with hR
  have hWF : ∑ s ∈ Ioc n0 n, (r s : ℝ) * (Real.log s ^ 2 / s)
      = ∑ s ∈ F, (r s : ℝ) * (Real.log s ^ 2 / s) := by
    rw [hF, Finset.sum_filter_of_ne]
    intro s _ h
    by_contra h'
    push Not at h'
    have : r s = 0 := by omega
    simp [this] at h
  have hCS := sq_sum_le_card_mul_sum_sq (s := F) (f := fun s => (r s : ℝ) * (Real.log s ^ 2 / s))
  have hterm : ∀ s ∈ F, ((r s : ℝ) * (Real.log s ^ 2 / s)) ^ 2 ≤ 81 * C s ^ 2 := by
    intro s hs
    simp only [hF, Finset.mem_filter, Finset.mem_Ioc] at hs
    have heven : Even s := by
      by_contra h
      have := s6_r_odd s h
      omega
    have h1 := hbig s hs.1.1
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (Real.exp_pos _) h1
    have hlog : 0 < Real.log s := Real.log_pos (by nlinarith [Real.add_one_le_exp (1000 : ℝ)])
    have hpb := pointwise_bound s heven h1
    have hup : (r s : ℝ) * (Real.log s ^ 2 / s) ≤ 9 * C s := by
      have hw : 0 < Real.log s ^ 2 / s := by positivity
      calc (r s : ℝ) * (Real.log s ^ 2 / s) ≤ 9 * C s * s / Real.log s ^ 2 * (Real.log s ^ 2 / s) :=
            mul_le_mul_of_nonneg_right hpb hw.le
        _ = 9 * C s := by field_simp
    have hlo : 0 ≤ (r s : ℝ) * (Real.log s ^ 2 / s) := by positivity
    calc ((r s : ℝ) * (Real.log s ^ 2 / s)) ^ 2 ≤ (9 * C s) ^ 2 := pow_le_pow_left₀ hlo hup 2
      _ = 81 * C s ^ 2 := by ring
  have hsumC : ∑ s ∈ F, C s ^ 2 ≤ 21 / 2 * (n : ℝ) := by
    have := C_mean (n : ℝ) (Nat.cast_nonneg n)
    rw [Nat.floor_natCast] at this
    refine le_trans ?_ this
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      simp only [hF, Finset.mem_filter, Finset.mem_Ioc] at hs
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, hs.1.2⟩, ?_⟩
      by_contra h
      have := s6_r_odd s h
      omega
    · intros; positivity
  have hFR : F.card ≤ R.card := by
    apply Finset.card_le_card
    intro s hs
    simp only [hF, hR, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hs ⊢
    exact ⟨by omega, hs.2⟩
  have hFR' : (F.card : ℝ) ≤ R.card := by exact_mod_cast hFR
  have hsq : ∑ s ∈ F, ((r s : ℝ) * (Real.log s ^ 2 / s)) ^ 2 ≤ 81 * (21 / 2 * (n : ℝ)) := by
    calc _ ≤ ∑ s ∈ F, 81 * C s ^ 2 := Finset.sum_le_sum hterm
      _ = 81 * ∑ s ∈ F, C s ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := by linarith
  rw [← hWF] at hCS
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hW2 : (443 / 1000 * (n : ℝ)) ^ 2 ≤ (∑ s ∈ Ioc n0 n, (r s : ℝ) * (Real.log s ^ 2 / s)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hW 2
  have hsq0 : 0 ≤ ∑ s ∈ F, ((r s : ℝ) * (Real.log s ^ 2 / s)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn
  have key : (443 / 1000 * (n : ℝ)) ^ 2 ≤ R.card * (81 * (21 / 2 * (n : ℝ))) := by
    calc _ ≤ _ := hW2
      _ ≤ _ := hCS
      _ ≤ (R.card : ℝ) * ∑ s ∈ F, ((r s : ℝ) * (Real.log s ^ 2 / s)) ^ 2 :=
          mul_le_mul_of_nonneg_right hFR' hsq0
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
  rw [div_le_iff₀ (by norm_num)]
  nlinarith


-- ===== part d =====

theorem s6d_zero_mem_B : 0 ∈ B := ⟨3, Nat.prime_three, by norm_num, rfl⟩

theorem s6d_B_sub_A : B ⊆ A := by
  intro b hb
  open Pointwise in exact Set.mem_add.2 ⟨0, s6d_zero_mem_B, b, hb, zero_add b⟩

theorem s6d_one_mem_A : 1 ∈ A :=
  s6d_B_sub_A ⟨5, by norm_num, by norm_num, rfl⟩

theorem s6d_odd_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.1 (hp.odd_of_ne_two h2)

open Classical in
/-- Medium range: `#(A ∩ [1,N]) + 2 ≥ π(2N+3)`. -/
theorem s6d_medium (N : ℕ) :
    Nat.primeCounting (2 * N + 3) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 2 := by
  set T := (range (2 * N + 4)).filter (fun p => p.Prime ∧ 5 ≤ p) with hT
  have h1 : Nat.primeCounting (2 * N + 3) ≤ #T + 2 := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    have hsub : (range (2 * N + 3 + 1)).filter Nat.Prime ⊆ insert 2 (insert 3 T) := by
      intro p hp
      simp only [mem_filter, mem_range] at hp
      simp only [mem_insert, hT, mem_filter, mem_range]
      by_cases h5 : 5 ≤ p
      · exact Or.inr (Or.inr ⟨by omega, hp.2, h5⟩)
      · have := hp.2.two_le
        interval_cases p
        · simp
        · simp
        · exact absurd hp.2 (by norm_num)
    refine (card_le_card hsub).trans ?_
    refine (card_insert_le _ _).trans ?_
    have := card_insert_le 3 T
    omega
  have h2 : #T ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
    have hinj : Set.InjOn (fun p => (p - 3) / 2) (T : Set ℕ) := by
      intro p hp q hq hpq
      simp only [hT, coe_filter, mem_range, Set.mem_ofPred_eq] at hp hq
      have := s6d_odd_of_prime hp.2.1 (by omega)
      have := s6d_odd_of_prime hq.2.1 (by omega)
      simp only at hpq
      omega
    rw [← card_image_of_injOn hinj]
    apply card_le_card
    intro a ha
    simp only [hT, mem_image, mem_filter, mem_range] at ha
    obtain ⟨p, ⟨hp1, hp2, hp3⟩, rfl⟩ := ha
    have := s6d_odd_of_prime hp2 (by omega)
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, s6d_B_sub_A ⟨p, hp2, by omega, rfl⟩⟩
  omega

open Classical in
/-- Large range: `#(A ∩ [1,N]) + 1 ≥ R(2N+6)`. -/
theorem s6d_large (N : ℕ) :
    #((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by
  set T := (range (2 * N + 6 + 1)).filter (fun s => 0 < r s) with hT
  have hmem : ∀ s ∈ T, ∃ p q, p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ q ≠ 2 ∧ s = p + q ∧ s ≤ 2 * N + 6 := by
    intro s hs
    simp only [hT, mem_filter, mem_range] at hs
    obtain ⟨hs1, hs2⟩ := hs
    unfold r at hs2
    obtain ⟨p, hp⟩ := card_pos.1 hs2
    simp only [mem_filter, mem_range] at hp
    exact ⟨p, s - p, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, by omega, by omega⟩
  have hinj : Set.InjOn (fun s => (s - 6) / 2) (T : Set ℕ) := by
    intro s hs t ht hst
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, -⟩ := hmem s hs
    obtain ⟨p', q', hp', hp2', hq', hq2', rfl, -⟩ := hmem t ht
    have := s6d_odd_of_prime hp hp2
    have := s6d_odd_of_prime hq hq2
    have := s6d_odd_of_prime hp' hp2'
    have := s6d_odd_of_prime hq' hq2'
    have := hp.two_le; have := hq.two_le; have := hp'.two_le; have := hq'.two_le
    simp only at hst
    omega
  rw [← card_image_of_injOn hinj]
  have hsub : T.image (fun s => (s - 6) / 2) ⊆ insert 0 ({a ∈ Ioc 0 N | a ∈ A}) := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := mem_image.1 ha
    obtain ⟨p, q, hp, hp2, hq, hq2, rfl, hle⟩ := hmem _ hs
    have := s6d_odd_of_prime hp hp2
    have := s6d_odd_of_prime hq hq2
    have := hp.two_le; have := hq.two_le
    rw [mem_insert, mem_filter, mem_Ioc]
    by_cases h0 : (p + q - 6) / 2 = 0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨by omega, by omega⟩, ?_⟩
      have : (p + q - 6) / 2 = (p - 3) / 2 + (q - 3) / 2 := by omega
      rw [this]
      open Pointwise in
      exact Set.mem_add.2 ⟨(p - 3) / 2, ⟨p, hp, hp2, rfl⟩, (q - 3) / 2, ⟨q, hq, hq2, rfl⟩, rfl⟩
  exact (card_le_card hsub).trans (card_insert_le _ _)

theorem s6d_two_mem_A : 2 ∈ A :=
  open Pointwise in Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 1, ⟨5, by norm_num, by norm_num, rfl⟩, rfl⟩

theorem s6d_three_mem_A : 3 ∈ A :=
  open Pointwise in Set.mem_add.2 ⟨1, ⟨5, by norm_num, by norm_num, rfl⟩, 2, ⟨7, by norm_num, by norm_num, rfl⟩, rfl⟩

open Classical in
/-- `σ(A) ≥ 1/2200`. -/
theorem s6_density_A : (1 : ℝ) / 2200 ≤ schnirelmannDensity A := by
  rw [le_schnirelmannDensity_iff]
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by norm_num) hNpos, one_mul]
  by_cases hsmall : N ≤ 6600
  · by_cases h3 : 3 ≤ N
    · have h1 : ({1, 2, 3} : Finset ℕ) ⊆ {a ∈ Ioc 0 N | a ∈ A} := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        simp only [mem_filter, mem_Ioc]
        rcases ha with rfl | rfl | rfl
        · exact ⟨⟨by norm_num, by omega⟩, s6d_one_mem_A⟩
        · exact ⟨⟨by norm_num, by omega⟩, s6d_two_mem_A⟩
        · exact ⟨⟨by norm_num, by omega⟩, s6d_three_mem_A⟩
      have h2 := card_le_card h1
      have h3' : (3 : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        have : ({1, 2, 3} : Finset ℕ).card = 3 := by rfl
        rw [this] at h2; exact_mod_cast h2
      have : (N : ℝ) ≤ 6600 := by exact_mod_cast hsmall
      linarith
    · have h1 : 1 ≤ #{a ∈ Ioc 0 N | a ∈ A} := by
        apply card_pos.2
        exact ⟨1, by simp only [mem_filter, mem_Ioc]; exact ⟨⟨by norm_num, hN⟩, s6d_one_mem_A⟩⟩
      have : (1 : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} := by exact_mod_cast h1
      have : (N : ℝ) ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
      linarith
  push Not at hsmall
  have hN' : (6601 : ℝ) ≤ N := by exact_mod_cast hsmall
  by_cases hbig : Real.exp 2000 ≤ ((2 * N + 6 : ℕ) : ℝ)
  · have hR := s6_R _ hbig
    have hL := s6d_large N
    have hL' : (#((range (2 * N + 6 + 1)).filter (fun s => 0 < r s)) : ℝ)
        ≤ #{a ∈ Ioc 0 N | a ∈ A} + 1 := by exact_mod_cast hL
    have hexp : (501 : ℝ) ^ 4 ≤ Real.exp 2000 := by
      have : Real.exp 2000 = Real.exp 500 ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have : (501 : ℝ) ≤ Real.exp 500 := by
        have := Real.add_one_le_exp (500 : ℝ); linarith
      gcongr
    push_cast at hR hbig
    nlinarith
  · push Not at hbig
    have hy : (1000 : ℝ) ≤ ((2 * N + 3 : ℕ) : ℝ) := by push_cast; linarith
    have hP := pi_lower _ hy
    rw [Nat.floor_natCast] at hP
    have hM := s6d_medium N
    have hM' : (Nat.primeCounting (2 * N + 3) : ℝ) ≤ #{a ∈ Ioc 0 N | a ∈ A} + 2 := by
      exact_mod_cast hM
    have hypos : (0 : ℝ) < ((2 * N + 3 : ℕ) : ℝ) := by linarith
    have hlog : Real.log ((2 * N + 3 : ℕ) : ℝ) < 2000 := by
      rw [Real.log_lt_iff_lt_exp hypos]
      push_cast at hbig ⊢; linarith
    have hlogpos : 0 < Real.log ((2 * N + 3 : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hfrac : 2 * ((2 * N + 3 : ℕ) : ℝ) / (3 * 2000) ≤
        2 * ((2 * N + 3 : ℕ) : ℝ) / (3 * Real.log ((2 * N + 3 : ℕ) : ℝ)) := by
      gcongr
    push_cast at hfrac hP
    nlinarith

open Pointwise

/-- Iterated sumsets `iter k = k A` (with `iter 0 = {0}`). -/
def s6m_iter : ℕ → Set ℕ
  | 0 => {0}
  | k + 1 => s6m_iter k + A

theorem s6m_zero_mem_A : (0 : ℕ) ∈ A :=
  Set.mem_add.2 ⟨0, ⟨3, Nat.prime_three, by norm_num, rfl⟩, 0, ⟨3, Nat.prime_three, by norm_num, rfl⟩,
    rfl⟩

theorem s6m_zero_mem_iter (k : ℕ) : 0 ∈ s6m_iter k := by
  induction k with
  | zero => rfl
  | succ k ih => exact Set.mem_add.2 ⟨0, ih, 0, s6m_zero_mem_A, rfl⟩

open Classical in
theorem s6m_density_iter (k : ℕ) :
    1 - (1 - schnirelmannDensity A) ^ k ≤ schnirelmannDensity (s6m_iter k) := by
  induction k with
  | zero => simp [schnirelmannDensity_nonneg]
  | succ k ih =>
    have h := schnirelmann_ineq (s6m_iter k) A (s6m_zero_mem_iter k) s6m_zero_mem_A
    have h1 : schnirelmannDensity A ≤ 1 := schnirelmannDensity_le_one
    have h2 : 0 ≤ 1 - schnirelmannDensity A := by linarith
    have h3 := mul_le_mul_of_nonneg_right (sub_le_comm.1 ih) h2
    show _ ≤ schnirelmannDensity (s6m_iter k + A)
    rw [pow_succ]
    nlinarith

theorem s6m_pow_bound (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 - 1 / 2200) : x ^ 1525 < 1 / 2 := by
  have hnat : 2 * 2199 ^ 1525 < 2200 ^ 1525 := by decide +kernel
  have hR : ((2 * 2199 ^ 1525 : ℕ) : ℝ) < ((2200 ^ 1525 : ℕ) : ℝ) := Nat.cast_lt.2 hnat
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow] at hR
  simp only [Nat.cast_ofNat] at hR
  have h1 : x ≤ (2199 : ℝ) / 2200 := by linarith
  have h2 : x ^ 1525 ≤ ((2199 : ℝ) / 2200) ^ 1525 := pow_le_pow_left₀ hx0 h1 _
  have h3 : ((2199 : ℝ) / 2200) ^ 1525 < 1 / 2 := by
    rw [div_pow, div_lt_iff₀ (by positivity)]
    generalize (2199 : ℝ) ^ 1525 = a at hR ⊢
    generalize (2200 : ℝ) ^ 1525 = b at hR ⊢
    linarith
  exact h2.trans_lt h3

/-- `P k t`: there are `k` odd primes summing to `2t + 3k`. -/
def s6m_P (k t : ℕ) : Prop :=
  ∃ s : Multiset ℕ, s.card = k ∧ (∀ p ∈ s, Nat.Prime p ∧ p ≠ 2) ∧ s.sum = 2 * t + 3 * k

theorem s6m_P_add {j k t u : ℕ} (h1 : s6m_P j t) (h2 : s6m_P k u) : s6m_P (j + k) (t + u) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := h1
  obtain ⟨s', hs1', hs2', hs3'⟩ := h2
  refine ⟨s + s', by simp [hs1, hs1'], fun p hp => ?_, by simp [hs3, hs3']; ring⟩
  rcases Multiset.mem_add.1 hp with h | h
  · exact hs2 p h
  · exact hs2' p h

theorem s6m_P_B {b : ℕ} (hb : b ∈ B) : s6m_P 1 b := by
  obtain ⟨p, hp, hp2, rfl⟩ := hb
  have := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have := hp.two_le
  refine ⟨{p}, by simp, fun q hq => ?_, ?_⟩
  · rw [Multiset.mem_singleton] at hq; subst hq; exact ⟨hp, hp2⟩
  · simp; omega

theorem s6m_P_A {a : ℕ} (ha : a ∈ A) : s6m_P 2 a := by
  obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_add.1 ha
  exact s6m_P_add (s6m_P_B hb) (s6m_P_B hc)

theorem s6m_P_iter (k : ℕ) : ∀ t ∈ s6m_iter k, s6m_P (2 * k) t := by
  induction k with
  | zero =>
    intro t ht
    rw [s6m_iter, Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨0, by simp, by simp, by simp⟩
  | succ k ih =>
    intro t ht
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 ht
    have := s6m_P_add (ih a ha) (s6m_P_A hb)
    rwa [show 2 * k + 2 = 2 * (k + 1) by ring] at this

open Classical in
theorem s6m_all (t : ℕ) : s6m_P 6100 t := by
  have hA := s6_density_A
  have h1 : schnirelmannDensity A ≤ 1 := schnirelmannDensity_le_one
  have h3 := s6m_pow_bound (1 - schnirelmannDensity A) (by linarith) (by linarith)
  have hd := s6m_density_iter 1525
  generalize (1 - schnirelmannDensity A) ^ 1525 = y at hd h3
  have h4 : (1 : ℝ) ≤ schnirelmannDensity (s6m_iter 1525) + schnirelmannDensity (s6m_iter 1525) := by
    linarith
  have huniv : s6m_iter 1525 + s6m_iter 1525 = Set.univ :=
    add_eq_univ_of_one_le_schirelmannDensity_add_schnirelmannDensity
      (s6m_zero_mem_iter _) (s6m_zero_mem_iter _) h4
  have ht : t ∈ s6m_iter 1525 + s6m_iter 1525 := by rw [huniv]; exact Set.mem_univ t
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 ht
  exact s6m_P_add (s6m_P_iter _ a ha) (s6m_P_iter _ b hb)

/-- Note, Theorem 1 (exact form): every odd `n ≥ 12203` is a sum of exactly `6101` primes. -/
theorem exact_6101 (n : ℕ) (hodd : Odd n) (hn : 12203 ≤ n) :
    ∃ s : Multiset ℕ, s.card = 6101 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  have hn2 := Nat.odd_iff.1 hodd
  by_cases hbig : 18303 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := s6m_all ((n - 18303) / 2)
    refine ⟨3 ::ₘ s, by simp [hs1], fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · exact (hs2 p h).1
    · rw [Multiset.sum_cons, hs3]; omega
  · refine ⟨Multiset.replicate (n - 12202) 3 + Multiset.replicate (18303 - n) 2,
      by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hp with h | h
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

end Schnir

/-- The campaign goal (platform theorem `odd_sum_le_6101_primes`). -/
theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 6101 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  by_cases hbig : 12203 ≤ n
  · obtain ⟨s, hs1, hs2, hs3⟩ := Schnir.exact_6101 n hodd hbig
    exact ⟨s, hs1.le, hs2, hs3⟩
  · have hn2 := Nat.odd_iff.1 hodd
    refine ⟨3 ::ₘ Multiset.replicate ((n - 3) / 2) 2, by simp; omega, fun p hp => ?_, ?_⟩
    · rcases Multiset.mem_cons.1 hp with h | h
      · rw [h]; exact Nat.prime_three
      · rw [Multiset.eq_of_mem_replicate h]; exact Nat.prime_two
    · simp; omega

