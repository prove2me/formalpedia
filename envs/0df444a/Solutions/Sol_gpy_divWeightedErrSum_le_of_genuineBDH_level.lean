-- Prove2me | solution 1 for gpy_divWeightedErrSum_le_of_genuineBDH_level
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T04:39:17.422208+00:00
-- url     : https://prove2.me/submissions/c208bf5e-93af-44a8-aa93-914deba612e0

/-
  Submission file for the Prove2Me problem `gpy_divWeightedErrSum_le_of_genuineBDH_level`
  (PubAll BDHFull batch, Oct 31, 2026).

  Self-contained: imports Mathlib only. Contains the verified bodies
  of the dependency chain plus the GPYBDHFull theorem `divWeightedErrSum_le_of_genuineBDH_level`,
  with top-level `theorem solution` in the problem's exact
  binder/statement form (all local definitions unfolded into
  Mathlib-only terms). No sorry tactic, no axioms beyond the
  standard ones, no platform imports.
  CONDITIONAL: the hBDH hypothesis is intact and unproved;
  nothing here proves genuine BDH or discharges hDiv.
-/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false



noncomputable def primeCountAP (Y L r : ℕ) : ℕ :=
  ((Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card

noncomputable def maxCoprimeErr (M : ℕ → ℕ → ℝ) (Y L : ℕ) : ℝ := by
  classical
  exact if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).max' h
    else 0

theorem coprimeResidues_nonempty {L : ℕ} (hLpos : 0 < L) :
    ((Finset.range L).filter (fun r => Nat.Coprime r L)).Nonempty := by
  by_cases hL1 : L = 1
  · subst hL1
    exact ⟨0, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by norm_num, by decide⟩⟩
  · exact ⟨1, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, Nat.coprime_one_left L⟩⟩

theorem maxCoprimeErr_nonneg (M : ℕ → ℕ → ℝ) (Y L : ℕ) :
    0 ≤ maxCoprimeErr M Y L := by
  classical
  unfold maxCoprimeErr
  by_cases himg : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).Nonempty
  · rw [dif_pos himg]
    obtain ⟨r₀, _, hr₀⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg)
    rw [← hr₀]
    exact abs_nonneg _
  · rw [dif_neg himg]

theorem sum_maxCoprimeErr_le_of_sum_bound (M : ℕ → ℕ → ℝ) (Y : ℕ) (S : Finset ℕ) (B : ℝ)
    (hB : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ S, abs ((primeCountAP Y q (v q) : ℝ) - M Y q) ≤ B) :
    ∑ L ∈ S, maxCoprimeErr M Y L ≤ B := by
  classical
  have hex : ∀ q : ℕ, ∃ r : ℕ, Nat.Coprime r q ∧
      maxCoprimeErr M Y q ≤ abs ((primeCountAP Y q r : ℝ) - M Y q) := by
    intro q
    by_cases hq0 : q = 0
    · subst hq0
      refine ⟨1, Nat.coprime_one_left 0, ?_⟩
      have hne0 : ¬ ((((Finset.range 0).filter (fun r => Nat.Coprime r 0)).image
          (fun r => abs ((primeCountAP Y 0 r : ℝ) - M Y 0)))).Nonempty := by
        rw [Finset.range_zero, Finset.filter_empty, Finset.image_empty]
        exact Finset.not_nonempty_empty
      unfold maxCoprimeErr
      rw [dif_neg hne0]
      exact abs_nonneg _
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      have himg := (coprimeResidues_nonempty hqpos).image
        (fun r => abs ((primeCountAP Y q r : ℝ) - M Y q))
      obtain ⟨r₀, hr₀mem, hr₀eq⟩ := Finset.mem_image.mp (Finset.max'_mem _ himg)
      refine ⟨r₀, (Finset.mem_filter.mp hr₀mem).2, ?_⟩
      unfold maxCoprimeErr
      rw [dif_pos himg, ← hr₀eq]
  choose v hvCop hvMax using hex
  calc ∑ L ∈ S, maxCoprimeErr M Y L
      ≤ ∑ L ∈ S, abs ((primeCountAP Y L (v L) : ℝ) - M Y L) :=
        Finset.sum_le_sum (fun L _ => hvMax L)
    _ ≤ B := hB v hvCop

theorem mem_bvRange_of_le_sq {Y R L : ℕ} {η : ℝ}
    (hL1 : 1 ≤ L) (hLR : L ≤ R ^ 2)
    (hlevel : (R : ℝ) ^ 2 < (Y : ℝ) ^ (1 / 2 - η)) :
    L ∈ (Finset.range ⌈(Y : ℝ) ^ (1 / 2 - η)⌉₊).filter
      (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y : ℝ) ^ (1 / 2 - η)) := by
  have hle : (L : ℝ) ≤ (R : ℝ) ^ 2 := by
    have h : (L : ℝ) ≤ ((R ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr hLR
    push_cast at h
    exact h
  have hlt : (L : ℝ) < (Y : ℝ) ^ (1 / 2 - η) := lt_of_le_of_lt hle hlevel
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hL1, hlt⟩
  have hceil : (L : ℝ) < ((⌈(Y : ℝ) ^ (1 / 2 - η)⌉₊ : ℕ) : ℝ) :=
    lt_of_lt_of_le hlt (Nat.le_ceil _)
  exact_mod_cast hceil

def tupleProdCount (k : ℕ) (D : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
    (fun d => ∏ i, d i = D)).card

theorem inv_succ_le_log_sub {d : ℕ} (hd : 1 ≤ d) :
    (1 : ℝ) / ((d : ℝ) + 1) ≤ Real.log ((d : ℝ) + 1) - Real.log (d : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hfrac : (0 : ℝ) < (d : ℝ) / ((d : ℝ) + 1) := by positivity
  have hle := Real.log_le_sub_one_of_pos hfrac
  rw [Real.log_div (ne_of_gt hdpos) (ne_of_gt (by positivity : (0 : ℝ) < (d : ℝ) + 1))] at hle
  have hdiv : (d : ℝ) / ((d : ℝ) + 1) - 1 = - (1 / ((d : ℝ) + 1)) := by
    field_simp
    ring
  rw [hdiv] at hle
  linarith

/-- The harmonic bound `∑_{d ≤ R} 1/d ≤ 1 + log R`, by induction. -/
theorem sum_Icc_inv_le : ∀ {R : ℕ}, 1 ≤ R →
    ∑ d ∈ Finset.Icc 1 R, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log (R : ℝ) := by
  intro R
  induction R with
  | zero => intro h; omega
  | succ n ih =>
    intro hR
    by_cases hn : n = 0
    · subst hn
      rw [Finset.Icc_self]
      simp
    · have hn1 : 1 ≤ n := by omega
      have ih' := ih hn1
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hstep : (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ≤
          Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) := by
        have h := inv_succ_le_log_sub (d := n) hn1
        push_cast at h ⊢
        exact h
      push_cast at hstep ⊢
      linarith

theorem tupleProdCount_succ {k D : ℕ} :
    tupleProdCount (k + 1) D = ∑ e ∈ Nat.divisors D, tupleProdCount k (D / e) := by
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · rw [hD0, Nat.divisors_zero, Finset.sum_empty]
    simp only [tupleProdCount]
    rw [Finset.card_eq_zero]
    ext d
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hd
    have h0 := (Fintype.mem_piFinset.mp hd.1) 0
    rw [Finset.mem_Icc] at h0
    omega
  · have hD1 : 1 ≤ D := hDpos
    -- The defining finset and its first-coordinate fibers.
    set S := (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 D)).filter
      (fun d => ∏ i, d i = D) with hS
    have hmaps : ∀ d ∈ S, d 0 ∈ Finset.Icc 1 D := by
      intro d hd
      rw [hS] at hd
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hd
      exact hd.1 0
    have hcard : S.card = ∑ e ∈ Finset.Icc 1 D,
        (S.filter (fun d => d 0 = e)).card := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
    -- Fiber cards.
    have hfib : ∀ e ∈ Finset.Icc 1 D, (S.filter (fun d => d 0 = e)).card
        = if e ∣ D then tupleProdCount k (D / e) else 0 := by
      intro e he
      rw [Finset.mem_Icc] at he
      by_cases hdiv : e ∣ D
      · rw [if_pos hdiv]
        have hepos : 0 < e := by
          rcases Nat.eq_zero_or_pos e with he0 | hepos
          · omega
          · exact hepos
        have heD : e ≤ D := Nat.le_of_dvd hDpos hdiv
        have hDe : D / e * e = D := Nat.div_mul_cancel hdiv
        have hDe1 : 1 ≤ D / e := by
          rw [Nat.le_div_iff_mul_le hepos]
          simpa using heD
        -- Bijection: tail / cons.
        have hbij : (S.filter (fun d => d 0 = e)).card
            = ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 (D / e))).filter
              (fun t => ∏ i, t i = D / e)).card := by
          apply Finset.card_bij (fun d _ => Fin.tail d)
          · intro d hd
            rw [Finset.mem_filter] at hd ⊢
            obtain ⟨hdS, hd0⟩ := hd
            rw [hS, Finset.mem_filter, Fintype.mem_piFinset] at hdS
            obtain ⟨hdmem, hdprod⟩ := hdS
            have htailprod : ∏ i, Fin.tail d i = D / e := by
              have h1 : ∏ i, d i = d 0 * ∏ i, Fin.tail d i := Fin.prod_univ_succ d
              rw [hd0, hdprod] at h1
              have h2 : e * ∏ i, Fin.tail d i = e * (D / e) := by
                rw [← h1, Nat.mul_div_cancel' hdiv]
              exact Nat.eq_of_mul_eq_mul_left hepos h2
            refine ⟨?_, htailprod⟩
            rw [Fintype.mem_piFinset]
            intro i
            rw [Finset.mem_Icc]
            have hmem : d i.succ ∈ Finset.Icc 1 D := hdmem i.succ
            rw [Finset.mem_Icc] at hmem
            refine ⟨hmem.1, ?_⟩
            have hdvd : d i.succ ∣ ∏ j, Fin.tail d j :=
              Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
            rw [htailprod] at hdvd
            exact Nat.le_of_dvd (by omega : 0 < D / e) hdvd
          · intro d hd e' hd' hde'
            rw [Finset.mem_filter] at hd hd'
            obtain ⟨-, hd0⟩ := hd
            obtain ⟨-, he'0⟩ := hd'
            have hd_eq : d = Fin.cons e (Fin.tail d) := by
              rw [← hd0]; exact (Fin.cons_self_tail d).symm
            have he'_eq : e' = Fin.cons e (Fin.tail e') := by
              rw [← he'0]; exact (Fin.cons_self_tail e').symm
            rw [hd_eq, he'_eq, hde']
          · intro t ht
            rw [Finset.mem_filter, Fintype.mem_piFinset] at ht
            obtain ⟨htmem, htprod⟩ := ht
            refine ⟨Fin.cons e t, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨?_, ?_⟩
              · rw [hS, Finset.mem_filter, Fintype.mem_piFinset]
                refine ⟨?_, ?_⟩
                · intro i
                  refine Fin.cases ?_ ?_ i
                  · rw [Fin.cons_zero]
                    exact Finset.mem_Icc.mpr ⟨he.1, heD⟩
                  · intro j
                    rw [Fin.cons_succ]
                    have hmi := htmem j
                    rw [Finset.mem_Icc] at hmi ⊢
                    exact ⟨hmi.1, le_trans hmi.2 (Nat.div_le_self D e)⟩
                · rw [Fin.prod_univ_succ, Fin.cons_zero]
                  simp only [Fin.cons_succ]
                  rw [htprod, Nat.mul_div_cancel' hdiv]
              · rw [Fin.cons_zero]
            · rw [Fin.tail_cons]
        rw [hbij]
        rfl
      · rw [if_neg hdiv]
        rw [Finset.card_eq_zero]
        ext d
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        intro hd
        obtain ⟨hdS, hd0⟩ := hd
        rw [hS, Finset.mem_filter] at hdS
        obtain ⟨-, hdprod⟩ := hdS
        have h1 : ∏ i, d i = d 0 * ∏ i, Fin.tail d i := Fin.prod_univ_succ d
        rw [hd0, hdprod] at h1
        exact hdiv ⟨∏ i, Fin.tail d i, h1⟩
    have hTS : tupleProdCount (k + 1) D = S.card := rfl
    rw [hTS, hcard]
    rw [Finset.sum_congr rfl hfib]
    rw [← Finset.sum_filter]
    congr 1

theorem sum_divisors_reindex (f : ℕ → ℝ) (R : ℕ) :
    ∑ D ∈ Finset.Icc 1 R, ∑ e ∈ Nat.divisors D, f (D / e)
      = ∑ e ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / e), f m := by
  have h1 : ∀ D ∈ Finset.Icc 1 R, ∑ e ∈ Nat.divisors D, f (D / e)
      = ∑ e ∈ Finset.Icc 1 R, (if e ∣ D then f (D / e) else 0) := by
    intro D hD
    rw [Finset.mem_Icc] at hD
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdiv, hD0⟩
      have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with he0 | hepos
        · rw [he0] at hdiv
          have hD00 : D = 0 := by simpa using hdiv
          exact (hD0 hD00).elim
        · exact hepos
      exact ⟨⟨he1, le_trans (Nat.le_of_dvd (by omega : 0 < D) hdiv) hD.2⟩, hdiv⟩
    · rintro ⟨⟨-, -⟩, hdiv⟩
      exact ⟨hdiv, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mem_Icc] at he
  by_cases he0 : e = 0
  · rw [he0] at he; omega
  · have hepos : 0 < e := Nat.pos_of_ne_zero he0
    have himg : (Finset.Icc 1 R).filter (fun D => e ∣ D)
        = (Finset.Icc 1 (R / e)).image (fun m => e * m) := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hD1, hDR⟩, hdiv⟩
        obtain ⟨m, rfl⟩ := hdiv
        refine ⟨m, ⟨?_, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos m with hm | hm
          · rw [hm] at hD1; simp at hD1
          · exact hm
        · exact (Nat.le_div_iff_mul_le hepos).mpr (by rwa [mul_comm])
      · rintro ⟨m, ⟨hm1, hmR⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
        · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        · have h := (Nat.le_div_iff_mul_le hepos).mp hmR
          rwa [mul_comm] at h
    have hinj : Set.InjOn (fun m => e * m) (Finset.Icc 1 (R / e)) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hepos hab
    rw [← Finset.sum_filter, himg, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro m _
    rw [mul_comm, Nat.mul_div_cancel _ hepos]

/-! ### Zero and one-fold counts -/

/-- `τ_{k+1}(0) = 0`: no tuple of positive integers has product `0`. -/
theorem tupleProdCount_succ_zero (k : ℕ) : tupleProdCount (k + 1) 0 = 0 := by
  simp only [tupleProdCount]
  rw [Finset.card_eq_zero]
  ext d
  simp only [Finset.notMem_empty, iff_false]
  intro hd
  rw [Finset.mem_filter, Fintype.mem_piFinset] at hd
  have h0 := hd.1 ⟨0, Nat.succ_pos k⟩
  rw [Finset.mem_Icc] at h0
  omega

/-- `τ_1(D) = 1` for `D ≥ 1`: the only 1-tuple with product `D` is `(D)`. -/
theorem tupleProdCount_one_eq_one {D : ℕ} (hD : 1 ≤ D) :
    tupleProdCount 1 D = 1 := by
  simp only [tupleProdCount]
  rw [Finset.card_eq_one]
  refine ⟨fun _ => D, ?_⟩
  ext d
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨hdmem, hdprod⟩
    rw [Fin.prod_univ_one] at hdprod
    funext i
    fin_cases i
    exact hdprod
  · intro hd
    rw [hd]
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      exact Finset.mem_Icc.mpr ⟨hD, le_rfl⟩
    · simp only [Fin.prod_univ_one]

/-- `τ_2(D)` is the divisor count. -/
theorem tupleProdCount_two_eq_card {D : ℕ} (hD : 1 ≤ D) :
    tupleProdCount 2 D = (Nat.divisors D).card := by
  rw [tupleProdCount_succ]
  have h : ∀ e ∈ Nat.divisors D, tupleProdCount 1 (D / e) = 1 := by
    intro e he
    rw [Nat.mem_divisors] at he
    have hepos : 0 < e := by
      rcases Nat.eq_zero_or_pos e with he0 | hepos
      · rw [he0] at he
        exact absurd (zero_dvd_iff.mp he.1) he.2
      · exact hepos
    have hle : e ≤ D := Nat.le_of_dvd (by omega) he.1
    have h1 : 1 ≤ D / e := Nat.div_pos hle hepos
    exact tupleProdCount_one_eq_one h1
  rw [Finset.sum_congr rfl h]
  simp [Finset.sum_const, smul_eq_mul]

/-! ### Monotonicity and submultiplicativity of `τ_2` -/

/-- `τ_2` is monotone under divisibility, by pair-scaling:
    `(a, b) ↦ (a, b·(L/d))` sends factorizations of `d` to
    factorizations of `L`. -/
theorem tupleProdCount_two_mono_of_dvd {d L : ℕ} (hd : 1 ≤ d) (hL : 1 ≤ L)
    (hdiv : d ∣ L) : tupleProdCount 2 d ≤ tupleProdCount 2 L := by
  have hdL : d ≤ L := Nat.le_of_dvd (by omega) hdiv
  have hLd : 1 ≤ L / d := Nat.div_pos hdL (by omega)
  have hmul : d * (L / d) = L := Nat.mul_div_cancel' hdiv
  have hcard_d : tupleProdCount 2 d =
      ((Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 d)).filter
        (fun t => ∏ i, t i = d)).card := rfl
  have hcard_L : tupleProdCount 2 L =
      ((Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 L)).filter
        (fun t => ∏ i, t i = L)).card := rfl
  rw [hcard_d, hcard_L]
  apply Finset.card_le_card_of_injOn (fun t => ![t 0, t 1 * (L / d)])
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at ht
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    have ht0 := Finset.mem_Icc.mp (ht.1 0)
    have ht1 := Finset.mem_Icc.mp (ht.1 1)
    have ht2 : t 0 * t 1 = d := by
      rw [← Fin.prod_univ_two]; exact ht.2
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      · exact Finset.mem_Icc.mpr ⟨ht0.1, le_trans ht0.2 hdL⟩
      · refine Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
        calc t 1 * (L / d) ≤ d * (L / d) :=
            mul_le_mul_of_nonneg_right ht1.2 (Nat.zero_le _)
          _ = L := hmul
    · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      calc t 0 * (t 1 * (L / d)) = (t 0 * t 1) * (L / d) := by ring
        _ = d * (L / d) := by rw [ht2]
        _ = L := hmul
  · intro t _ t' _ h
    have h0 : t 0 = t' 0 := by
      have hcon := congrFun h 0
      simpa [Matrix.cons_val_zero] using hcon
    have h1 : t 1 * (L / d) = t' 1 * (L / d) := by
      have hcon := congrFun h 1
      simpa [Matrix.cons_val_one, Matrix.head_cons] using hcon
    have h1' : t 1 = t' 1 := Nat.eq_of_mul_eq_mul_right (by omega) h1
    funext i
    fin_cases i
    · exact h0
    · exact h1'

/-- Gcd-splitting of a factorization: if `a * b = d * m`, then writing
    `g = gcd a d`, `a2 = a / g`, `d1 = d / g`, `m2 = m / a2` splits the
    factorization into one of `d` and one of `m`. -/
theorem pair_split_aux {a b d m g a2 d1 m2 : ℕ}
    (hd : 1 ≤ d) (hm : 1 ≤ m) (h : a * b = d * m) (ha : 1 ≤ a)
    (hg : g = Nat.gcd a d) (ha2 : a2 = a / g) (hd1 : d1 = d / g)
    (hm2 : m2 = m / a2) :
    g * a2 = a ∧ g * d1 = d ∧ a2 * m2 = m ∧ d1 * m2 = b ∧
    1 ≤ g ∧ g ≤ d ∧ 1 ≤ d1 ∧ d1 ≤ d ∧ 1 ≤ a2 ∧ a2 ≤ m ∧
    1 ≤ m2 ∧ m2 ≤ m := by
  subst hg ha2 hd1 hm2
  have hgpos : 0 < Nat.gcd a d :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left a d) (by omega)
  have hga : Nat.gcd a d * (a / Nat.gcd a d) = a :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left a d)
  have hgd : Nat.gcd a d * (d / Nat.gcd a d) = d :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right a d)
  have hcop : Nat.Coprime (a / Nat.gcd a d) (d / Nat.gcd a d) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have key : (a / Nat.gcd a d) * b = (d / Nat.gcd a d) * m := by
    apply Nat.eq_of_mul_eq_mul_left hgpos
    calc Nat.gcd a d * ((a / Nat.gcd a d) * b)
        = (Nat.gcd a d * (a / Nat.gcd a d)) * b := by rw [mul_assoc]
      _ = a * b := by rw [hga]
      _ = d * m := h
      _ = (Nat.gcd a d * (d / Nat.gcd a d)) * m := by rw [hgd]
      _ = Nat.gcd a d * ((d / Nat.gcd a d) * m) := by rw [mul_assoc]
  have ha2dvd : (a / Nat.gcd a d) ∣ m :=
    hcop.dvd_of_dvd_mul_left ⟨b, key.symm⟩
  have ha2pos : 0 < a / Nat.gcd a d :=
    Nat.pos_of_dvd_of_pos ha2dvd (by omega)
  have ham : (a / Nat.gcd a d) * (m / (a / Nat.gcd a d)) = m :=
    Nat.mul_div_cancel' ha2dvd
  have hbm : (d / Nat.gcd a d) * (m / (a / Nat.gcd a d)) = b := by
    apply Nat.eq_of_mul_eq_mul_left ha2pos
    calc (a / Nat.gcd a d) * ((d / Nat.gcd a d) * (m / (a / Nat.gcd a d)))
        = (d / Nat.gcd a d) * ((a / Nat.gcd a d) * (m / (a / Nat.gcd a d))) := by ring
      _ = (d / Nat.gcd a d) * m := by rw [ham]
      _ = (a / Nat.gcd a d) * b := key.symm
  refine ⟨hga, hgd, ham, hbm, hgpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right a d)
  · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right a d)) hgpos
  · exact Nat.div_le_self d _
  · exact ha2pos
  · exact Nat.le_of_dvd (by omega) ha2dvd
  · exact Nat.div_pos (Nat.le_of_dvd (by omega) ha2dvd) ha2pos
  · exact Nat.div_le_self m _

/-- `τ_2` is submultiplicative, by the gcd-splitting injection. -/
theorem tupleProdCount_two_submul {d m : ℕ} :
    tupleProdCount 2 (d * m) ≤ tupleProdCount 2 d * tupleProdCount 2 m := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [hd0, zero_mul, tupleProdCount_succ_zero]
    exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hm0, mul_zero, tupleProdCount_succ_zero]
    exact Nat.zero_le _
  have hd : 1 ≤ d := hdpos
  have hm : 1 ≤ m := hmpos
  have hcard : ∀ D : ℕ, tupleProdCount 2 D =
      ((Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 D)).filter
        (fun t => ∏ i, t i = D)).card := fun D => rfl
  rw [hcard, hcard, hcard, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn
    (fun t => (![Nat.gcd (t 0) d, d / Nat.gcd (t 0) d],
      ![t 0 / Nat.gcd (t 0) d, m / (t 0 / Nat.gcd (t 0) d)]))
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at ht
    have ht0 := Finset.mem_Icc.mp (ht.1 0)
    have ht2 : t 0 * t 1 = d * m := by
      rw [← Fin.prod_univ_two]; exact ht.2
    obtain ⟨hga, hgd, ham, hbm, hg1, hg_le, hd1, hd1_le, ha2, ha2_le, hm2, hm2_le⟩ :=
      pair_split_aux hd hm ht2 ht0.1 rfl rfl rfl rfl
    rw [Finset.mem_coe, Finset.mem_product]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        · exact Finset.mem_Icc.mpr ⟨hg1, hg_le⟩
        · exact Finset.mem_Icc.mpr ⟨hd1, hd1_le⟩
      · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        exact hgd
    · rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        · exact Finset.mem_Icc.mpr ⟨ha2, ha2_le⟩
        · exact Finset.mem_Icc.mpr ⟨hm2, hm2_le⟩
      · simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        exact ham
  · intro t ht t' ht' h
    have htmem := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
    rw [Fintype.mem_piFinset] at htmem
    have ht0 := Finset.mem_Icc.mp (htmem.1 0)
    have ht2 : t 0 * t 1 = d * m := by
      rw [← Fin.prod_univ_two]; exact htmem.2
    have ht'mem := Finset.mem_filter.mp (Finset.mem_coe.mp ht')
    rw [Fintype.mem_piFinset] at ht'mem
    have ht'0 := Finset.mem_Icc.mp (ht'mem.1 0)
    have ht'2 : t' 0 * t' 1 = d * m := by
      rw [← Fin.prod_univ_two]; exact ht'mem.2
    obtain ⟨hga, -, -, hbm, -, -, -, -, -, -, -, -⟩ :=
      pair_split_aux hd hm ht2 ht0.1 rfl rfl rfl rfl
    obtain ⟨hga', -, -, hbm', -, -, -, -, -, -, -, -⟩ :=
      pair_split_aux hd hm ht'2 ht'0.1 rfl rfl rfl rfl
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    have hg_eq : Nat.gcd (t 0) d = Nat.gcd (t' 0) d := by
      have hcon := congrFun hfst 0
      simpa [Matrix.cons_val_zero] using hcon
    have hd1_eq : d / Nat.gcd (t 0) d = d / Nat.gcd (t' 0) d := by
      have hcon := congrFun hfst 1
      simpa [Matrix.cons_val_one, Matrix.head_cons] using hcon
    have ha2_eq : t 0 / Nat.gcd (t 0) d = t' 0 / Nat.gcd (t' 0) d := by
      have hcon := congrFun hsnd 0
      simpa [Matrix.cons_val_zero] using hcon
    have hm2_eq : m / (t 0 / Nat.gcd (t 0) d) = m / (t' 0 / Nat.gcd (t' 0) d) := by
      have hcon := congrFun hsnd 1
      simpa [Matrix.cons_val_one, Matrix.head_cons] using hcon
    have ht0_eq : t 0 = t' 0 := by rw [← hga, ← hga', ha2_eq, hg_eq]
    have ht1_eq : t 1 = t' 1 := by rw [← hbm, ← hbm', hm2_eq, hd1_eq]
    funext i
    fin_cases i
    · exact ht0_eq
    · exact ht1_eq

/-! ### Comparing `τ_{k+1}` with a power of `τ_2` -/

/-- `τ_{k+1}(L) ≤ τ_2(L)^k`, by induction on `k` using the convolution
    identity and monotonicity of `τ_2` under divisibility. -/
theorem tupleProdCount_le_tau_two_pow : ∀ (k : ℕ) {L : ℕ}, 1 ≤ L →
    tupleProdCount (k + 1) L ≤ (tupleProdCount 2 L) ^ k := by
  intro k
  induction k with
  | zero =>
    intro L hL
    simp [pow_zero, tupleProdCount_one_eq_one hL]
  | succ k ih =>
    intro L hL
    have hstep : tupleProdCount (k + 1 + 1) L
        = ∑ e ∈ Nat.divisors L, tupleProdCount (k + 1) (L / e) :=
      tupleProdCount_succ
    rw [hstep]
    calc ∑ e ∈ Nat.divisors L, tupleProdCount (k + 1) (L / e)
        ≤ ∑ e ∈ Nat.divisors L, (tupleProdCount 2 L) ^ k := by
          apply Finset.sum_le_sum
          intro e he
          rw [Nat.mem_divisors] at he
          have hepos : 0 < e := by
            rcases Nat.eq_zero_or_pos e with he0 | hepos
            · rw [he0] at he
              exact absurd (zero_dvd_iff.mp he.1) he.2
            · exact hepos
          have hle : e ≤ L := Nat.le_of_dvd (by omega) he.1
          have h1 : 1 ≤ L / e := Nat.div_pos hle hepos
          have hdvd : L / e ∣ L := ⟨e, by rw [mul_comm]; exact (Nat.mul_div_cancel' he.1).symm⟩
          calc tupleProdCount (k + 1) (L / e)
              ≤ (tupleProdCount 2 (L / e)) ^ k := ih h1
            _ ≤ (tupleProdCount 2 L) ^ k :=
                pow_le_pow_left₀ (by positivity)
                  (tupleProdCount_two_mono_of_dvd h1 hL hdvd) k
      _ = (tupleProdCount 2 L) ^ (k + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← tupleProdCount_two_eq_card hL,
            pow_succ]
          exact mul_comm _ _

/-! ### Divisor reindexing for a summand depending on `D` -/

/-- Reindexing: summing `G(D)` over `e ∣ D`, `D ≤ R`, is the same as
    summing `G(e·m)` over `m ≤ R/e`, `e ≤ R`. (Variant of
    `sum_divisors_reindex` for a summand depending on `D` itself.) -/
theorem sum_divisors_sum_reindex (G : ℕ → ℝ) (R : ℕ) :
    ∑ D ∈ Finset.Icc 1 R, ∑ e ∈ Nat.divisors D, G D
      = ∑ e ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / e), G (e * m) := by
  have h1 : ∀ D ∈ Finset.Icc 1 R, ∑ e ∈ Nat.divisors D, G D
      = ∑ e ∈ Finset.Icc 1 R, (if e ∣ D then G D else 0) := by
    intro D hD
    rw [Finset.mem_Icc] at hD
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdiv, hD0⟩
      have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with he0 | hepos
        · rw [he0] at hdiv
          have hD00 : D = 0 := by simpa using hdiv
          exact (hD0 hD00).elim
        · exact hepos
      exact ⟨⟨he1, le_trans (Nat.le_of_dvd (by omega : 0 < D) hdiv) hD.2⟩, hdiv⟩
    · rintro ⟨⟨-, -⟩, hdiv⟩
      exact ⟨hdiv, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mem_Icc] at he
  by_cases he0 : e = 0
  · rw [he0] at he; omega
  · have hepos : 0 < e := Nat.pos_of_ne_zero he0
    have himg : (Finset.Icc 1 R).filter (fun D => e ∣ D)
        = (Finset.Icc 1 (R / e)).image (fun m => e * m) := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hD1, hDR⟩, hdiv⟩
        obtain ⟨m, rfl⟩ := hdiv
        refine ⟨m, ⟨?_, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos m with hm | hm
          · rw [hm] at hD1; simp at hD1
          · exact hm
        · exact (Nat.le_div_iff_mul_le hepos).mpr (by rwa [mul_comm])
      · rintro ⟨m, ⟨hm1, hmR⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
        · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        · have h := (Nat.le_div_iff_mul_le hepos).mp hmR
          rwa [mul_comm] at h
    have hinj : Set.InjOn (fun m => e * m) (Finset.Icc 1 (R / e)) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hepos hab
    rw [← Finset.sum_filter, himg, Finset.sum_image hinj]

/-! ### Reciprocal power moments -/

/-- Auxiliary: `τ_2` as a real divisor sum. -/
theorem tau_two_eq_sum_one_real {d : ℕ} (hd : 1 ≤ d) :
    (tupleProdCount 2 d : ℝ) = ∑ e ∈ Nat.divisors d, (1 : ℝ) := by
  rw [tupleProdCount_two_eq_card hd]
  simp [Finset.sum_const]

/-- `U_1(Q) := ∑_{d ≤ Q} τ_2(d)/d ≤ (1 + log Q)^2`, from the harmonic
    bound alone via the divisor reindexing. -/
theorem sum_tau_div_le {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) / (d : ℝ)
      ≤ (1 + Real.log (Q : ℝ)) ^ 2 := by
  have hlognn : (0 : ℝ) ≤ 1 + Real.log (Q : ℝ) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ (Q : ℝ) by exact_mod_cast hQ)
    linarith
  calc ∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) / (d : ℝ)
      = ∑ d ∈ Finset.Icc 1 Q, ∑ e ∈ Nat.divisors d, (1 : ℝ) / (d : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mem_Icc] at hd
        rw [tau_two_eq_sum_one_real hd.1, Finset.sum_div]
    _ = ∑ e ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 (Q / e),
          (1 : ℝ) / ((e * m : ℕ) : ℝ) :=
        sum_divisors_sum_reindex (fun D => (1 : ℝ) / (D : ℝ)) Q
    _ ≤ ∑ e ∈ Finset.Icc 1 Q, (1 : ℝ) / (e : ℝ) * (1 + Real.log (Q : ℝ)) := by
        apply Finset.sum_le_sum
        intro e he
        rw [Finset.mem_Icc] at he
        have hQe : 1 ≤ Q / e :=
          (Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr (by simpa using he.2)
        have hinner : ∑ m ∈ Finset.Icc 1 (Q / e), (1 : ℝ) / ((e * m : ℕ) : ℝ)
            = (1 : ℝ) / (e : ℝ) * ∑ m ∈ Finset.Icc 1 (Q / e), (1 : ℝ) / (m : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          push_cast
          rw [div_mul_div_comm, one_mul]
        rw [hinner]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_trans
          (Finset.sum_le_sum_of_subset_of_nonneg (by
            intro m hm
            rw [Finset.mem_Icc] at hm ⊢
            exact ⟨hm.1, le_trans hm.2 (Nat.div_le_self Q e)⟩)
            (by intro m _ _; positivity))
          (sum_Icc_inv_le hQ)
    _ = (1 + Real.log (Q : ℝ)) * ∑ e ∈ Finset.Icc 1 Q, (1 : ℝ) / (e : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro _ _
        rw [mul_comm]
    _ ≤ (1 + Real.log (Q : ℝ)) * (1 + Real.log (Q : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_inv_le hQ) hlognn
    _ = (1 + Real.log (Q : ℝ)) ^ 2 := by rw [pow_two]

/-- The reciprocal power moments `U_r(Q) ≤ (1 + log Q)^(2^r)`, by
    induction on `r` using submultiplicativity and the reindexing.
    (The recursion `U_{r+1} ≤ U_r^2` is what produces the `2^r`.) -/
theorem sum_tau_pow_div_le : ∀ (r : ℕ) {Q : ℕ}, 1 ≤ Q →
    ∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) ^ r / (d : ℝ)
      ≤ (1 + Real.log (Q : ℝ)) ^ (2 ^ r) := by
  intro r
  induction r with
  | zero =>
    intro Q hQ
    simp only [pow_zero]
    rw [pow_one]
    exact sum_Icc_inv_le hQ
  | succ r ih =>
    intro Q hQ
    have hlognn : (0 : ℝ) ≤ 1 + Real.log (Q : ℝ) := by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ (Q : ℝ) by exact_mod_cast hQ)
      linarith
    have hU_nn : ∀ {Q' : ℕ},
        0 ≤ ∑ d ∈ Finset.Icc 1 Q', (tupleProdCount 2 d : ℝ) ^ r / (d : ℝ) := by
      intro Q'
      apply Finset.sum_nonneg
      intro d _
      positivity
    have hterm : ∀ d : ℕ, (tupleProdCount 2 d : ℝ) ^ r
          * (∑ e ∈ Nat.divisors d, (1 : ℝ)) / (d : ℝ)
        = ∑ e ∈ Nat.divisors d, (tupleProdCount 2 d : ℝ) ^ r / (d : ℝ) := by
      intro d
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _
      rw [mul_one]
    have hstep1 : ∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) ^ (r + 1) / (d : ℝ)
        = ∑ d ∈ Finset.Icc 1 Q, ∑ e ∈ Nat.divisors d,
            (tupleProdCount 2 d : ℝ) ^ r / (d : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_Icc] at hd
      calc (tupleProdCount 2 d : ℝ) ^ (r + 1) / (d : ℝ)
          = ((tupleProdCount 2 d : ℝ) ^ r * (tupleProdCount 2 d : ℝ)) / (d : ℝ) := by
            rw [pow_succ]
        _ = ((tupleProdCount 2 d : ℝ) ^ r * ∑ e ∈ Nat.divisors d, (1 : ℝ)) / (d : ℝ) := by
            rw [tau_two_eq_sum_one_real hd.1]
        _ = ∑ e ∈ Nat.divisors d, (tupleProdCount 2 d : ℝ) ^ r / (d : ℝ) := hterm d
    rw [hstep1, sum_divisors_sum_reindex]
    calc ∑ e ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 (Q / e),
            (tupleProdCount 2 (e * m) : ℝ) ^ r / ((e * m : ℕ) : ℝ)
        ≤ ∑ e ∈ Finset.Icc 1 Q, (tupleProdCount 2 e : ℝ) ^ r / (e : ℝ) *
            ∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) ^ r / (d : ℝ) := by
          apply Finset.sum_le_sum
          intro e he
          rw [Finset.mem_Icc] at he
          have hQe : 1 ≤ Q / e :=
            (Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr (by simpa using he.2)
          calc ∑ m ∈ Finset.Icc 1 (Q / e),
                  (tupleProdCount 2 (e * m) : ℝ) ^ r / ((e * m : ℕ) : ℝ)
              ≤ ∑ m ∈ Finset.Icc 1 (Q / e),
                  ((tupleProdCount 2 e : ℝ) ^ r / (e : ℝ)) *
                    ((tupleProdCount 2 m : ℝ) ^ r / (m : ℝ)) := by
                apply Finset.sum_le_sum
                intro m hm
                rw [Finset.mem_Icc] at hm
                have hsub : (tupleProdCount 2 (e * m) : ℝ) ^ r
                    ≤ ((tupleProdCount 2 e : ℝ) * (tupleProdCount 2 m : ℝ)) ^ r :=
                  pow_le_pow_left₀ (by positivity)
                    (by exact_mod_cast tupleProdCount_two_submul) r
                rw [mul_pow] at hsub
                have hdiv : (tupleProdCount 2 (e * m) : ℝ) ^ r / ((e * m : ℕ) : ℝ)
                    ≤ ((tupleProdCount 2 e : ℝ) ^ r * (tupleProdCount 2 m : ℝ) ^ r)
                      / ((e * m : ℕ) : ℝ) := by
                  rw [div_eq_mul_inv, div_eq_mul_inv]
                  exact mul_le_mul_of_nonneg_right hsub (by positivity)
                refine le_trans hdiv ?_
                push_cast
                rw [div_mul_div_comm]
            _ ≤ (tupleProdCount 2 e : ℝ) ^ r / (e : ℝ) *
                ∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) ^ r / (d : ℝ) := by
                rw [← Finset.mul_sum]
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro m hm
                  rw [Finset.mem_Icc] at hm ⊢
                  exact ⟨hm.1, le_trans hm.2 (Nat.div_le_self Q e)⟩
                · intro m _ _
                  positivity
      _ = (∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) ^ r / (d : ℝ)) *
            (∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) ^ r / (d : ℝ)) := by
          rw [← Finset.sum_mul]
      _ ≤ ((1 + Real.log (Q : ℝ)) ^ (2 ^ r)) * ((1 + Real.log (Q : ℝ)) ^ (2 ^ r)) :=
          mul_le_mul (ih hQ) (ih hQ) hU_nn (pow_nonneg hlognn _)
      _ = (1 + Real.log (Q : ℝ)) ^ (2 ^ (r + 1)) := by
          rw [← pow_add]
          congr 1
          rw [pow_succ]
          ring

/-! ### Power moments -/

/-- The power moments `T_r(Q) ≤ Q·(1 + log Q)^(2^r - 1)`, by induction
    on `r` using `U_{r-1}`. (For `r = 4` the exponent is `2^4 - 1 = 15`,
    the classical exponent for the fourth moment of `τ`.) -/
theorem sum_tau_pow_le : ∀ (r : ℕ) {Q : ℕ}, 1 ≤ Q →
    ∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) ^ r
      ≤ (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ r - 1) := by
  intro r
  induction r with
  | zero =>
    intro Q hQ
    calc ∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) ^ 0
        = (Q : ℝ) := by
          simp only [pow_zero]
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc,
            Nat.add_sub_cancel]
      _ ≤ (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ 0 - 1) := by
          simp
  | succ r ih =>
    intro Q hQ
    have hlognn : (0 : ℝ) ≤ 1 + Real.log (Q : ℝ) := by
      have h := Real.log_nonneg (show (1 : ℝ) ≤ (Q : ℝ) by exact_mod_cast hQ)
      linarith
    have hstep1 : ∑ d ∈ Finset.Icc 1 Q, (tupleProdCount 2 d : ℝ) ^ (r + 1)
        = ∑ d ∈ Finset.Icc 1 Q, ∑ e ∈ Nat.divisors d,
            (tupleProdCount 2 d : ℝ) ^ r := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_Icc] at hd
      calc (tupleProdCount 2 d : ℝ) ^ (r + 1)
          = (tupleProdCount 2 d : ℝ) ^ r * (tupleProdCount 2 d : ℝ) := pow_succ _ _
        _ = (tupleProdCount 2 d : ℝ) ^ r * ∑ e ∈ Nat.divisors d, (1 : ℝ) := by
            rw [tau_two_eq_sum_one_real hd.1]
        _ = ∑ e ∈ Nat.divisors d, (tupleProdCount 2 d : ℝ) ^ r * 1 :=
            Finset.mul_sum ..
        _ = ∑ e ∈ Nat.divisors d, (tupleProdCount 2 d : ℝ) ^ r := by
            apply Finset.sum_congr rfl
            intro e _
            rw [mul_one]
    rw [hstep1, sum_divisors_sum_reindex]
    calc ∑ e ∈ Finset.Icc 1 Q, ∑ m ∈ Finset.Icc 1 (Q / e),
            (tupleProdCount 2 (e * m) : ℝ) ^ r
        ≤ ∑ e ∈ Finset.Icc 1 Q, (tupleProdCount 2 e : ℝ) ^ r * ((Q : ℝ) / (e : ℝ)) *
            (1 + Real.log (Q : ℝ)) ^ (2 ^ r - 1) := by
          apply Finset.sum_le_sum
          intro e he
          rw [Finset.mem_Icc] at he
          have hQe : 1 ≤ Q / e :=
            (Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr (by simpa using he.2)
          have hinner : ∑ m ∈ Finset.Icc 1 (Q / e), (tupleProdCount 2 (e * m) : ℝ) ^ r
              ≤ (tupleProdCount 2 e : ℝ) ^ r *
                  (((Q / e : ℕ) : ℝ) * (1 + Real.log ((Q / e : ℕ) : ℝ)) ^ (2 ^ r - 1)) := by
            calc ∑ m ∈ Finset.Icc 1 (Q / e), (tupleProdCount 2 (e * m) : ℝ) ^ r
                ≤ (tupleProdCount 2 e : ℝ) ^ r *
                    ∑ m ∈ Finset.Icc 1 (Q / e), (tupleProdCount 2 m : ℝ) ^ r := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_le_sum
                  intro m _
                  have hsub : (tupleProdCount 2 (e * m) : ℝ) ^ r
                      ≤ ((tupleProdCount 2 e : ℝ) * (tupleProdCount 2 m : ℝ)) ^ r :=
                    pow_le_pow_left₀ (by positivity)
                      (by exact_mod_cast tupleProdCount_two_submul) r
                  rw [mul_pow] at hsub
                  exact hsub
              _ ≤ (tupleProdCount 2 e : ℝ) ^ r *
                  (((Q / e : ℕ) : ℝ) * (1 + Real.log ((Q / e : ℕ) : ℝ)) ^ (2 ^ r - 1)) :=
                  mul_le_mul_of_nonneg_left (ih hQe) (by positivity)
          refine le_trans hinner ?_
          have hbase_nn : (0 : ℝ) ≤ 1 + Real.log ((Q / e : ℕ) : ℝ) := by
            have h := Real.log_nonneg (show (1 : ℝ) ≤ ((Q / e : ℕ) : ℝ) by exact_mod_cast hQe)
            linarith
          have hbase_le : 1 + Real.log ((Q / e : ℕ) : ℝ) ≤ 1 + Real.log (Q : ℝ) := by
            have hle : ((Q / e : ℕ) : ℝ) ≤ (Q : ℝ) := by
              exact_mod_cast Nat.div_le_self Q e
            have hpos : (0 : ℝ) < ((Q / e : ℕ) : ℝ) := by exact_mod_cast hQe
            have hll := Real.log_le_log hpos hle
            linarith
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul Nat.cast_div_le (pow_le_pow_left₀ hbase_nn hbase_le _)
              (pow_nonneg hbase_nn _) (by positivity)) (by positivity)
      _ = (1 + Real.log (Q : ℝ)) ^ (2 ^ r - 1) *
            ((Q : ℝ) * ∑ e ∈ Finset.Icc 1 Q, (tupleProdCount 2 e : ℝ) ^ r / (e : ℝ)) := by
          have hterm : ∀ e ∈ Finset.Icc 1 Q,
              (tupleProdCount 2 e : ℝ) ^ r * ((Q : ℝ) / (e : ℝ)) *
                (1 + Real.log (Q : ℝ)) ^ (2 ^ r - 1)
              = (1 + Real.log (Q : ℝ)) ^ (2 ^ r - 1) *
                  ((Q : ℝ) * ((tupleProdCount 2 e : ℝ) ^ r / (e : ℝ))) := by
            intro e he
            rw [Finset.mem_Icc] at he
            have hne : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
            field_simp
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (1 + Real.log (Q : ℝ)) ^ (2 ^ r - 1) *
            ((Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ r)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_tau_pow_div_le r hQ
      _ = (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ (r + 1) - 1) := by
          have hring : (1 + Real.log (Q : ℝ)) ^ (2 ^ r - 1) *
                ((Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ r))
              = (Q : ℝ) * ((1 + Real.log (Q : ℝ)) ^ (2 ^ r - 1) *
                  (1 + Real.log (Q : ℝ)) ^ (2 ^ r)) := by ring
          have hexp : (2 ^ r - 1) + 2 ^ r = 2 ^ (r + 1) - 1 := by
            have hpos : 1 ≤ 2 ^ r :=
              Nat.one_le_iff_ne_zero.mpr (pow_ne_zero r (show (2 : ℕ) ≠ 0 by norm_num))
            rw [pow_succ, mul_two]
            exact (Nat.sub_add_comm hpos).symm
          rw [hring, ← pow_add]
          congr 1
          congr 1

/-! ### The main fourth-order bound -/

/-- THE MAIN BOUND, in `Icc` form: `∑_{L ≤ Q} τ_{k+1}(L)^4
    ≤ Q·(1 + log Q)^(2^(4k) - 1)`. The exponent is explicit; for the
    classical case `k = 1` (i.e. `τ_2` itself) it is `2^4 - 1 = 15`. -/
theorem sum_tupleProdCount_pow_four_le (k : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ L ∈ Finset.Icc 1 Q, (tupleProdCount (k + 1) L : ℝ) ^ 4
      ≤ (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ (4 * k) - 1) := by
  calc ∑ L ∈ Finset.Icc 1 Q, (tupleProdCount (k + 1) L : ℝ) ^ 4
      ≤ ∑ L ∈ Finset.Icc 1 Q, (tupleProdCount 2 L : ℝ) ^ (4 * k) := by
        apply Finset.sum_le_sum
        intro L hL
        rw [Finset.mem_Icc] at hL
        have hle : tupleProdCount (k + 1) L ≤ (tupleProdCount 2 L) ^ k :=
          tupleProdCount_le_tau_two_pow k hL.1
        have hleR : (tupleProdCount (k + 1) L : ℝ) ≤ (tupleProdCount 2 L : ℝ) ^ k := by
          exact_mod_cast hle
        calc (tupleProdCount (k + 1) L : ℝ) ^ 4
            ≤ ((tupleProdCount 2 L : ℝ) ^ k) ^ 4 :=
              pow_le_pow_left₀ (by positivity) hleR 4
          _ = (tupleProdCount 2 L : ℝ) ^ (4 * k) := by
              rw [← pow_mul, Nat.mul_comm k 4]
    _ ≤ (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ (4 * k) - 1) :=
        sum_tau_pow_le (4 * k) hQ

/-- THE MAIN BOUND, in the `range (Q+1)` form used by
    `divWeightedErrSum` (the `L = 0` term vanishes). -/
theorem sum_tupleProdCount_pow_four_range_le (k : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ L ∈ Finset.range (Q + 1), (tupleProdCount (k + 1) L : ℝ) ^ 4
      ≤ (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ (4 * k) - 1) := by
  have h0 : (tupleProdCount (k + 1) 0 : ℝ) ^ 4 = 0 := by
    rw [tupleProdCount_succ_zero]
    simp
  have hsum : ∀ Q : ℕ, ∑ L ∈ Finset.range (Q + 1), (tupleProdCount (k + 1) L : ℝ) ^ 4
      = (tupleProdCount (k + 1) 0 : ℝ) ^ 4
        + ∑ L ∈ Finset.Icc 1 Q, (tupleProdCount (k + 1) L : ℝ) ^ 4 := by
    intro Q
    induction Q with
    | zero =>
      rw [Finset.sum_range_one]
      have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, add_zero]
    | succ Q ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ Q + 1)]
      ring
  rw [hsum, h0, zero_add]
  exact sum_tupleProdCount_pow_four_le k hQ

/-! ### The Cauchy–Schwarz bridge to `hDiv` -/

/-- Generic Cauchy–Schwarz bridge: the divisor-weighted error sum with
    weight `τ_{k+1}(L)^2` is controlled by the fourth-order τ-moment
    and the second moment of the errors. Combined with the main bound
    above and a BDH-type bound `∑ e(L)^2 ≪ Y'^2·polylog·log^{-A'}`,
    this yields `hDiv` — the BDH input is the remaining missing piece,
    not proved here. -/
theorem sum_tau_sq_mul_sq_le (e : ℕ → ℝ) (k Q : ℕ) :
    (∑ L ∈ Finset.range (Q + 1), (tupleProdCount (k + 1) L : ℝ) ^ 2 * e L) ^ 2
      ≤ (∑ L ∈ Finset.range (Q + 1), (tupleProdCount (k + 1) L : ℝ) ^ 4)
        * (∑ L ∈ Finset.range (Q + 1), (e L) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (Q + 1))
    (fun L => (tupleProdCount (k + 1) L : ℝ) ^ 2) e
  refine le_trans h ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  apply Finset.sum_le_sum
  intro L _
  exact le_of_eq (by ring :
    ((tupleProdCount (k + 1) L : ℝ) ^ 2) ^ 2
      = (tupleProdCount (k + 1) L : ℝ) ^ 4)

noncomputable def divWeightedErrSum (M : ℕ → ℕ → ℝ) (Y' Q : ℕ) (k : ℕ) : ℝ :=
  ∑ L ∈ Finset.range (Q + 1), (tupleProdCount (k + 1) L : ℝ) ^ 2 * maxCoprimeErr M Y' L

theorem sum_maxCoprimeErr_sq_le_of_sum_bound (M : ℕ → ℕ → ℝ) (Y' Q : ℕ) {B : ℝ}
    (hBnn : 0 ≤ B)
    (hsum : ∑ L ∈ Finset.range (Q + 1), maxCoprimeErr M Y' L ≤ B) :
    ∑ L ∈ Finset.range (Q + 1), (maxCoprimeErr M Y' L) ^ 2 ≤ B ^ 2 := by
  classical
  have hterm : ∀ L ∈ Finset.range (Q + 1),
      (maxCoprimeErr M Y' L) ^ 2 ≤ B * maxCoprimeErr M Y' L := by
    intro L hL
    have hle : maxCoprimeErr M Y' L ≤ B :=
      le_trans (Finset.single_le_sum (fun i _ => maxCoprimeErr_nonneg M Y' i) hL) hsum
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hle (maxCoprimeErr_nonneg M Y' L)
  calc ∑ L ∈ Finset.range (Q + 1), (maxCoprimeErr M Y' L) ^ 2
      ≤ ∑ L ∈ Finset.range (Q + 1), B * maxCoprimeErr M Y' L :=
        Finset.sum_le_sum hterm
    _ = B * ∑ L ∈ Finset.range (Q + 1), maxCoprimeErr M Y' L := by
        rw [Finset.mul_sum]
    _ ≤ B * B := mul_le_mul_of_nonneg_left hsum hBnn
    _ = B ^ 2 := by rw [pow_two]

theorem sum_maxCoprimeErr_le_of_bvSumBound_range (M : ℕ → ℕ → ℝ) (Y' R : ℕ)
    {η : ℝ} (B : ℝ)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y' q (v q) : ℝ) - M Y' q) ≤ B) :
    ∑ L ∈ Finset.range (R ^ 2 + 1), maxCoprimeErr M Y' L ≤ B := by
  classical
  have hmax0 : maxCoprimeErr M Y' 0 = 0 := by
    have hne0 : ¬ ((((Finset.range 0).filter (fun r => Nat.Coprime r 0)).image
        (fun r => abs ((primeCountAP Y' 0 r : ℝ) - M Y' 0)))).Nonempty := by
      rw [Finset.range_zero, Finset.filter_empty, Finset.image_empty]
      exact Finset.not_nonempty_empty
    unfold maxCoprimeErr
    rw [dif_neg hne0]
  have hsplit : (∑ L ∈ Finset.range (R ^ 2 + 1), maxCoprimeErr M Y' L)
      = ∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L : ℕ => 1 ≤ L),
        maxCoprimeErr M Y' L := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (R ^ 2 + 1))
      (fun L : ℕ => 1 ≤ L) (fun L => maxCoprimeErr M Y' L)]
    have hnot : (∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L : ℕ => ¬ 1 ≤ L),
        maxCoprimeErr M Y' L) = 0 := by
      apply Finset.sum_eq_zero
      intro L hL
      rw [Finset.mem_filter] at hL
      have hL0 : L = 0 := by omega
      rw [hL0, hmax0]
    rw [hnot, add_zero]
  rw [hsplit]
  calc (∑ L ∈ (Finset.range (R ^ 2 + 1)).filter (fun L : ℕ => 1 ≤ L),
          maxCoprimeErr M Y' L)
      ≤ ∑ L ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        maxCoprimeErr M Y' L := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro L hL
          rw [Finset.mem_filter, Finset.mem_range] at hL
          exact mem_bvRange_of_le_sq hL.2 (by omega) hlev
        · intro L _ _
          exact maxCoprimeErr_nonneg _ _ _
    _ ≤ B := sum_maxCoprimeErr_le_of_sum_bound M Y' _ _ hBV

theorem sum_maxCoprimeErr_sq_le_of_bvSumBound (M : ℕ → ℕ → ℝ) (Y' R : ℕ)
    {η : ℝ} (B : ℝ)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y' q (v q) : ℝ) - M Y' q) ≤ B) :
    ∑ L ∈ Finset.range (R ^ 2 + 1), (maxCoprimeErr M Y' L) ^ 2 ≤ B ^ 2 := by
  classical
  have hBnn : 0 ≤ B := by
    have hsum := hBV (fun _ => 1) (fun q => Nat.coprime_one_left q)
    exact le_trans (Finset.sum_nonneg (fun q _ => abs_nonneg _)) hsum
  exact sum_maxCoprimeErr_sq_le_of_sum_bound M Y' (R ^ 2) hBnn
    (sum_maxCoprimeErr_le_of_bvSumBound_range M Y' R B hlev hBV)

theorem divWeightedErrSum_sq_le_of_bvSumBound (M : ℕ → ℕ → ℝ) (Y' R : ℕ) (k : ℕ)
    {η : ℝ} (B : ℝ) (hR : 1 ≤ R)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y' q (v q) : ℝ) - M Y' q) ≤ B) :
    (divWeightedErrSum M Y' (R ^ 2) k) ^ 2
      ≤ ((R : ℝ) ^ 2 * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1)) * B ^ 2 := by
  classical
  have hR2 : 1 ≤ R ^ 2 := by
    have hle := pow_le_pow_left₀ (show (0 : ℕ) ≤ 1 by norm_num) hR 2
    simpa using hle
  have htau := sum_tupleProdCount_pow_four_range_le k hR2
  push_cast at htau
  have hcs := sum_tau_sq_mul_sq_le (fun L => maxCoprimeErr M Y' L) k (R ^ 2)
  have hbdh := sum_maxCoprimeErr_sq_le_of_bvSumBound M Y' R B hlev hBV
  have hnn1 : 0 ≤ ∑ L ∈ Finset.range (R ^ 2 + 1), (maxCoprimeErr M Y' L) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hRr : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hR2r : (1 : ℝ) ≤ (R : ℝ) ^ 2 := by
    have hle := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hRr 2
    simpa using hle
  have hlognn : 0 ≤ Real.log ((R : ℝ) ^ 2) := Real.log_nonneg hR2r
  have hnn2 : 0 ≤ (R : ℝ) ^ 2 * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
  calc (divWeightedErrSum M Y' (R ^ 2) k) ^ 2
      = (∑ L ∈ Finset.range (R ^ 2 + 1),
          (tupleProdCount (k + 1) L : ℝ) ^ 2 * maxCoprimeErr M Y' L) ^ 2 := rfl
    _ ≤ (∑ L ∈ Finset.range (R ^ 2 + 1), (tupleProdCount (k + 1) L : ℝ) ^ 4)
        * (∑ L ∈ Finset.range (R ^ 2 + 1), (maxCoprimeErr M Y' L) ^ 2) := hcs
    _ ≤ ((R : ℝ) ^ 2 * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1)) * B ^ 2 :=
        mul_le_mul htau hbdh hnn1 hnn2

theorem divWeightedErrSum_le_of_bvSumBound_bdh (M : ℕ → ℕ → ℝ) (Y' R : ℕ) (k : ℕ)
    {η : ℝ} (B : ℝ) (hR : 1 ≤ R) (hBnn : 0 ≤ B)
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBV : ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((primeCountAP Y' q (v q) : ℝ) - M Y' q) ≤ B) :
    divWeightedErrSum M Y' (R ^ 2) k
      ≤ (R : ℝ) * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k)) * B := by
  classical
  have hsq := divWeightedErrSum_sq_le_of_bvSumBound M Y' R k B hR hlev hBV
  have hRr : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hR2r : (1 : ℝ) ≤ (R : ℝ) ^ 2 := by
    have hle := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hRr 2
    simpa using hle
  have hlognn : 0 ≤ Real.log ((R : ℝ) ^ 2) := Real.log_nonneg hR2r
  have hbase1 : (1 : ℝ) ≤ 1 + Real.log ((R : ℝ) ^ 2) := by linarith
  have hbase_nn : 0 ≤ 1 + Real.log ((R : ℝ) ^ 2) := by linarith
  have hXnn : 0 ≤ (R : ℝ) * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k)) * B :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hbase_nn _)) hBnn
  have hdivnn : 0 ≤ divWeightedErrSum M Y' (R ^ 2) k := by
    have heq : divWeightedErrSum M Y' (R ^ 2) k
        = ∑ L ∈ Finset.range (R ^ 2 + 1),
          (tupleProdCount (k + 1) L : ℝ) ^ 2 * maxCoprimeErr M Y' L := rfl
    rw [heq]
    apply Finset.sum_nonneg
    intro L _
    exact mul_nonneg (by positivity) (maxCoprimeErr_nonneg _ _ _)
  have hexp : 2 ^ (4 * k) - 1 ≤ 2 * (2 ^ (4 * k)) := by
    have hp : 0 < 2 ^ (4 * k) := pow_pos (by norm_num) _
    omega
  have hpowle : (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1)
      ≤ (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 * (2 ^ (4 * k))) :=
    pow_le_pow_right₀ hbase1 hexp
  have hXsq : ((R : ℝ) * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k)) * B) ^ 2
      = (R : ℝ) ^ 2 * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 * (2 ^ (4 * k))) * B ^ 2 := by
    rw [show 2 * (2 ^ (4 * k)) = (2 ^ (4 * k)) * 2 from mul_comm _ _, pow_mul]
    ring
  have hle : (divWeightedErrSum M Y' (R ^ 2) k) ^ 2
      ≤ ((R : ℝ) * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k)) * B) ^ 2 := by
    rw [hXsq]
    exact le_trans hsq
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowle (by positivity)) (sq_nonneg B))
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hXnn hle

/-- The bridge: at one modulus, the squared max coprime-residue
    error is at most the sum of the squared errors over all coprime
    residues. The max is attained at some coprime residue, and its
    squared error is one nonnegative term of the sum. -/
theorem maxCoprimeErr_sq_le_sum_sq (M : ℕ → ℕ → ℝ) (Y L : ℕ) :
    (maxCoprimeErr M Y L) ^ 2 ≤
      ∑ r ∈ (Finset.range L).filter (fun r => Nat.Coprime r L),
        (abs ((primeCountAP Y L r : ℝ) - M Y L)) ^ 2 := by
  classical
  by_cases h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).Nonempty
  · have hmem : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
        (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).max' h ∈
      (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
        (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))) :=
      Finset.max'_mem _ h
    obtain ⟨r₀, hr₀, hr₀eq⟩ := Finset.mem_image.mp hmem
    have hr₀eq' : abs ((primeCountAP Y L r₀ : ℝ) - M Y L) =
        (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
          (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).max' h := hr₀eq
    have hmax : maxCoprimeErr M Y L =
        (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
          (fun r => abs ((primeCountAP Y L r : ℝ) - M Y L))).max' h := by
      unfold maxCoprimeErr
      rw [dif_pos h]
    rw [hmax, ← hr₀eq']
    exact Finset.single_le_sum
      (fun i _ => sq_nonneg (abs ((primeCountAP Y L i : ℝ) - M Y L))) hr₀
  · have hmax : maxCoprimeErr M Y L = 0 := by
      unfold maxCoprimeErr
      rw [dif_neg h]
    rw [hmax]
    have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [h0]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- The bridge summed over moduli: the second moment of the max
    errors is at most the summed squared-error second moment. -/
theorem sum_maxCoprimeErr_sq_le_sum_sum_sq (M : ℕ → ℕ → ℝ) (Y Q : ℕ) :
    ∑ L ∈ Finset.range (Q + 1), (maxCoprimeErr M Y L) ^ 2 ≤
      ∑ L ∈ Finset.range (Q + 1), ∑ r ∈ (Finset.range L).filter
          (fun r => Nat.Coprime r L),
        (abs ((primeCountAP Y L r : ℝ) - M Y L)) ^ 2 :=
  Finset.sum_le_sum (fun L _ => maxCoprimeErr_sq_le_sum_sq M Y L)

/-- Squared conditional discharge: under a genuine BDH hypothesis
    in the exact summed form (full range `L ≤ R²`, all coprime
    residues, explicit constants `D` and polylog exponent `E`),
    the squared divisor-weighted sum is at most the τ⁴ bound times
    the BDH bound. -/
theorem divWeightedErrSum_sq_le_of_genuineBDH (M : ℕ → ℕ → ℝ) (Y' R : ℕ) (k : ℕ)
    (D : ℝ) (E : ℕ) (_hD : 0 ≤ D) (hR : 1 ≤ R) (_hY : 1 ≤ Y')
    (hBDH : ∑ L ∈ Finset.range (R ^ 2 + 1),
        ∑ r ∈ (Finset.range L).filter (fun r => Nat.Coprime r L),
          (abs ((primeCountAP Y' L r : ℝ) - M Y' L)) ^ 2
        ≤ D * ((R : ℝ) ^ 2 * (Y' : ℝ) * (1 + Real.log (Y' : ℝ)) ^ E)) :
    (divWeightedErrSum M Y' (R ^ 2) k) ^ 2 ≤
      ((R : ℝ) ^ 2 * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1)) *
        (D * ((R : ℝ) ^ 2 * (Y' : ℝ) * (1 + Real.log (Y' : ℝ)) ^ E)) := by
  classical
  have hR2 : 1 ≤ R ^ 2 := by
    have hle := pow_le_pow_left₀ (show (0 : ℕ) ≤ 1 by norm_num) hR 2
    simpa using hle
  have htau := sum_tupleProdCount_pow_four_range_le k hR2
  push_cast at htau
  have hmax : ∑ L ∈ Finset.range (R ^ 2 + 1), (maxCoprimeErr M Y' L) ^ 2 ≤
      D * ((R : ℝ) ^ 2 * (Y' : ℝ) * (1 + Real.log (Y' : ℝ)) ^ E) :=
    le_trans (sum_maxCoprimeErr_sq_le_sum_sum_sq M Y' (R ^ 2)) hBDH
  have hcs := sum_tau_sq_mul_sq_le (fun L => maxCoprimeErr M Y' L) k (R ^ 2)
  have hnn1 : 0 ≤ ∑ L ∈ Finset.range (R ^ 2 + 1), (maxCoprimeErr M Y' L) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hRr : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hR2r : (1 : ℝ) ≤ (R : ℝ) ^ 2 := by
    have hle := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hRr 2
    simpa using hle
  have hlognn : 0 ≤ Real.log ((R : ℝ) ^ 2) := Real.log_nonneg hR2r
  have hnn2 : 0 ≤ (R : ℝ) ^ 2 * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
  have hdiv : divWeightedErrSum M Y' (R ^ 2) k =
      ∑ L ∈ Finset.range (R ^ 2 + 1),
        (tupleProdCount (k + 1) L : ℝ) ^ 2 * maxCoprimeErr M Y' L := rfl
  rw [hdiv]
  calc (∑ L ∈ Finset.range (R ^ 2 + 1),
          (tupleProdCount (k + 1) L : ℝ) ^ 2 * maxCoprimeErr M Y' L) ^ 2
      ≤ (∑ L ∈ Finset.range (R ^ 2 + 1), (tupleProdCount (k + 1) L : ℝ) ^ 4)
        * (∑ L ∈ Finset.range (R ^ 2 + 1), (maxCoprimeErr M Y' L) ^ 2) := hcs
    _ ≤ ((R : ℝ) ^ 2 * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1)) *
        (D * ((R : ℝ) ^ 2 * (Y' : ℝ) * (1 + Real.log (Y' : ℝ)) ^ E)) :=
        mul_le_mul htau hmax hnn1 hnn2

/-- Unsquared conditional discharge: under the genuine BDH
    hypothesis, the divisor-weighted sum is at most
    `R² · √Y' · √polylog` with the polylog factor explicit. -/
theorem divWeightedErrSum_le_of_genuineBDH (M : ℕ → ℕ → ℝ) (Y' R : ℕ) (k : ℕ)
    (D : ℝ) (E : ℕ) (hD : 0 ≤ D) (hR : 1 ≤ R) (hY : 1 ≤ Y')
    (hBDH : ∑ L ∈ Finset.range (R ^ 2 + 1),
        ∑ r ∈ (Finset.range L).filter (fun r => Nat.Coprime r L),
          (abs ((primeCountAP Y' L r : ℝ) - M Y' L)) ^ 2
        ≤ D * ((R : ℝ) ^ 2 * (Y' : ℝ) * (1 + Real.log (Y' : ℝ)) ^ E)) :
    divWeightedErrSum M Y' (R ^ 2) k ≤
      (R : ℝ) ^ 2 * Real.sqrt (Y' : ℝ) *
        Real.sqrt (D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) *
          (1 + Real.log (Y' : ℝ)) ^ E) := by
  classical
  have hsq := divWeightedErrSum_sq_le_of_genuineBDH M Y' R k D E hD hR hY hBDH
  have hYnn : (0 : ℝ) ≤ (Y' : ℝ) := by exact_mod_cast (Nat.zero_le Y')
  have hRr : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hR2r : (1 : ℝ) ≤ (R : ℝ) ^ 2 := by
    have hle := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hRr 2
    simpa using hle
  have hlogRnn : (0 : ℝ) ≤ 1 + Real.log ((R : ℝ) ^ 2) := by
    have h := Real.log_nonneg hR2r
    linarith
  have hlogYnn : (0 : ℝ) ≤ 1 + Real.log (Y' : ℝ) := by
    have h : (1 : ℝ) ≤ (Y' : ℝ) := by exact_mod_cast hY
    have hl := Real.log_nonneg h
    linarith
  have hPnn : (0 : ℝ) ≤ D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) *
      (1 + Real.log (Y' : ℝ)) ^ E :=
    mul_nonneg (mul_nonneg hD (pow_nonneg hlogRnn _)) (pow_nonneg hlogYnn _)
  have hXnn : (0 : ℝ) ≤ (R : ℝ) ^ 2 * Real.sqrt (Y' : ℝ) *
      Real.sqrt (D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) *
        (1 + Real.log (Y' : ℝ)) ^ E) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hXsq : ((R : ℝ) ^ 2 * Real.sqrt (Y' : ℝ) *
      Real.sqrt (D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) *
        (1 + Real.log (Y' : ℝ)) ^ E)) ^ 2 =
      ((R : ℝ) ^ 2 * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1)) *
        (D * ((R : ℝ) ^ 2 * (Y' : ℝ) * (1 + Real.log (Y' : ℝ)) ^ E)) := by
    simp only [mul_pow, Real.sq_sqrt hYnn, Real.sq_sqrt hPnn]
    ring
  have hle : (divWeightedErrSum M Y' (R ^ 2) k) ^ 2 ≤
      ((R : ℝ) ^ 2 * Real.sqrt (Y' : ℝ) *
        Real.sqrt (D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) *
          (1 + Real.log (Y' : ℝ)) ^ E)) ^ 2 := by
    rw [hXsq]
    exact hsq
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hXnn hle

/-- Level corollary: under the level constraint `R² < Y'^{1/2−η}`,
    the `R² · √Y'` factor collapses to `Y'^{1−η}`, so the
    divisor-weighted sum is at most `Y'^{1−η} · √polylog` — the
    power saving that the trivial bound missed by exactly `R`.
    The remaining step to `hDiv`'s `Cw · Y' · log^{−A''}` is only
    the asymptotic threshold inequality `Y'^{−η} · √polylog ≤
    const · log(Y')^{−A''}` for `Y'` large, stated here as a gap,
    not proved and not hidden. -/
theorem divWeightedErrSum_le_of_genuineBDH_level (M : ℕ → ℕ → ℝ) (Y' R : ℕ) (k : ℕ)
    {η : ℝ} (D : ℝ) (E : ℕ) (hD : 0 ≤ D) (hR : 1 ≤ R) (hY : 1 ≤ Y')
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBDH : ∑ L ∈ Finset.range (R ^ 2 + 1),
        ∑ r ∈ (Finset.range L).filter (fun r => Nat.Coprime r L),
          (abs ((primeCountAP Y' L r : ℝ) - M Y' L)) ^ 2
        ≤ D * ((R : ℝ) ^ 2 * (Y' : ℝ) * (1 + Real.log (Y' : ℝ)) ^ E)) :
    divWeightedErrSum M Y' (R ^ 2) k ≤
      (Y' : ℝ) ^ (1 - η) *
        Real.sqrt (D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) *
          (1 + Real.log (Y' : ℝ)) ^ E) := by
  classical
  have hmain := divWeightedErrSum_le_of_genuineBDH M Y' R k D E hD hR hY hBDH
  have hYpos : (0 : ℝ) < (Y' : ℝ) := by
    have h : (1 : ℝ) ≤ (Y' : ℝ) := by exact_mod_cast hY
    linarith
  have hsqrtY : Real.sqrt (Y' : ℝ) = (Y' : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hle1 : (R : ℝ) ^ 2 * Real.sqrt (Y' : ℝ) ≤ (Y' : ℝ) ^ (1 - η) := by
    rw [hsqrtY]
    have hmul := mul_lt_mul_of_pos_right hlev (Real.rpow_pos_of_pos hYpos (1 / 2 : ℝ))
    have hrw : (Y' : ℝ) ^ (1 / 2 - η) * (Y' : ℝ) ^ (1 / 2 : ℝ) = (Y' : ℝ) ^ (1 - η) := by
      rw [← Real.rpow_add hYpos]
      congr 1
      ring
    rw [hrw] at hmul
    exact le_of_lt hmul
  calc divWeightedErrSum M Y' (R ^ 2) k
      ≤ (R : ℝ) ^ 2 * Real.sqrt (Y' : ℝ) *
          Real.sqrt (D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) *
            (1 + Real.log (Y' : ℝ)) ^ E) := hmain
    _ ≤ (Y' : ℝ) ^ (1 - η) *
          Real.sqrt (D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) *
            (1 + Real.log (Y' : ℝ)) ^ E) :=
        mul_le_mul_of_nonneg_right hle1 (Real.sqrt_nonneg _)

/-- The diagonal second moment of the von Mangoldt function:
    `∑_{n ≤ N} Λ(n)² ≤ (log 4 + 4) · N · log N`. Each term satisfies
    `Λ(n)² = Λ(n) · Λ(n) ≤ Λ(n) · log N` (since `Λ(n) ≤ log n ≤
    log N` and `Λ(n) ≥ 0`), and `∑_{n ≤ N} Λ(n) = ψ(N) ≤
    (log 4 + 4) · N` is Mathlib's Chebyshev bound. This is the
    diagonal input a large-sieve proof of BDH consumes; it is not
    BDH itself. -/
theorem sum_vonMangoldt_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt n) ^ 2 ≤
      (Real.log 4 + 4) * (N : ℝ) * Real.log (N : ℝ) := by
  classical
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogNnn : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hterm : ∀ n ∈ Finset.Icc 0 N,
      (ArithmeticFunction.vonMangoldt n) ^ 2 ≤
        ArithmeticFunction.vonMangoldt n * Real.log (N : ℝ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hΛnn : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hΛle : ArithmeticFunction.vonMangoldt n ≤ Real.log (N : ℝ) := by
      by_cases hn0 : n = 0
      · rw [hn0]
        have h0 : ArithmeticFunction.vonMangoldt 0 ≤ Real.log ((0 : ℕ) : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
        simp only [Nat.cast_zero, Real.log_zero] at h0
        exact le_trans h0 hlogNnn
      · have hn1 : 1 ≤ n := by omega
        have hle1 : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
        have hn0' : 0 < n := by omega
        have hle2 : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
          Real.log_le_log (by exact_mod_cast hn0') (by exact_mod_cast hn.2)
        exact le_trans hle1 hle2
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hΛle hΛnn
  have hpsi : (∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n) =
      Chebyshev.psi (N : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  calc ∑ n ∈ Finset.Icc 0 N, (ArithmeticFunction.vonMangoldt n) ^ 2
      ≤ ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n * Real.log (N : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n) * Real.log (N : ℝ) := by
        rw [Finset.sum_mul]
    _ = Chebyshev.psi (N : ℝ) * Real.log (N : ℝ) := by rw [hpsi]
    _ ≤ ((Real.log 4 + 4) * (N : ℝ)) * Real.log (N : ℝ) :=
        mul_le_mul_of_nonneg_right
          (Chebyshev.psi_le_const_mul_self (by positivity : (0 : ℝ) ≤ (N : ℝ))) hlogNnn
    _ = (Real.log 4 + 4) * (N : ℝ) * Real.log (N : ℝ) := by ring

theorem solution (M : ℕ → ℕ → ℝ) (Y' R : ℕ) (k : ℕ)
    {η : ℝ} (D : ℝ) (E : ℕ) (hD : 0 ≤ D) (hR : 1 ≤ R) (hY : 1 ≤ Y')
    (hlev : (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η))
    (hBDH : ∑ L ∈ Finset.range (R ^ 2 + 1),
        ∑ r ∈ (Finset.range L).filter (fun r => Nat.Coprime r L),
          (abs (((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y' L)) ^ 2
        ≤ D * ((R : ℝ) ^ 2 * (Y' : ℝ) * (1 + Real.log (Y' : ℝ)) ^ E)) :
    ∑ L ∈ Finset.range (R ^ 2 + 1), (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 (L))).filter (fun t => ∏ i, t i = (L))).card : ℝ) ^ 2 * (if h : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs (((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y' L))).Nonempty then
    (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
      (fun r => abs (((((Finset.range (Y' + 1)).filter (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y' L))).max' h
    else 0) ≤
      (Y' : ℝ) ^ (1 - η) *
        Real.sqrt (D * (1 + Real.log ((R : ℝ) ^ 2)) ^ (2 ^ (4 * k) - 1) * (1 + Real.log (Y' : ℝ)) ^ E) := by
  exact divWeightedErrSum_le_of_genuineBDH_level M Y' R k D E hD hR hY hlev hBDH
