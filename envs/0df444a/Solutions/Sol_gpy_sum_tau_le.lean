-- Prove2me | solution 1 for gpy_sum_tau_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T19:19:51.969713+00:00
-- url     : https://prove2.me/submissions/19cdff6d-edfc-4d64-a011-37290ff93bd4

/-
  Submission file for the Prove2Me problem `sum_tau_le`
  (tau-moment bound, restated form).

  Self-contained: imports Mathlib only. Contains the verified bodies of
  GPYWeights.lean (tupleSupport), GPYLambdaSelberg.lean (lamSelberg,
  tupleProdCount, the τ-weighted λ-mass identity), and GPYTauMoments.lean,
  with top-level `theorem solution` in the problem's exact binder/statement
  form (statement mechanically extracted from the restated theorem, so the
  two are textually identical modulo the theorem name).
  No sorry tactic, no axioms beyond the standard ones, no platform imports.
-/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

namespace GPY

/-- The support set for tuple Selberg weights at level R: tuples of positive
    integers, each at most R, whose product is at most R. -/
def tupleSupport (k : ℕ) (R : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)


/-- Membership in the support set, unfolded. -/
theorem mem_tupleSupport {k : ℕ} {R : ℕ} {d : Fin k → ℕ} :
    d ∈ tupleSupport k R ↔
      (∀ i, 1 ≤ d i) ∧ (∀ i, d i ≤ R) ∧ ∏ i, d i ≤ R := by
  rw [tupleSupport, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (Finset.mem_Icc.mp (h1 i)).1,
      fun i => (Finset.mem_Icc.mp (h1 i)).2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨h1 i, h2 i⟩, h3⟩


/-- Classical GPY/Selberg tuple weight of degree `deg`: the Möbius
    function of the total product times the polynomial cutoff
    `(1 - log D / log R)^deg`, supported where `D ≤ R`. -/
noncomputable def lamSelberg (k : ℕ) (R : ℕ) (deg : ℕ) (d : Fin k → ℕ) : ℝ :=
  if ∏ i, d i ≤ R then
    (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
      * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
  else 0


/-- On the support, the weight is the μ-times-polynomial form. -/
theorem lamSelberg_eq_of_mem_support {k R deg : ℕ} {d : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) :
    lamSelberg k R deg d
      = (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
        * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg := by
  unfold lamSelberg
  rw [if_pos (mem_tupleSupport.mp hd).2.2]


/-- Number of ordered factorizations of `D` into `k` positive factors:
    the `k`-fold divisor function `τ_k(D)` in the form the sums need.
    (Each factor is at most `D` automatically when the product is `D`
    and all factors are positive, so `Icc 1 D` is the right range.) -/
def tupleProdCount (k : ℕ) (D : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
    (fun d => ∏ i, d i = D)).card


/-- The fiber of the support over a product `D ≤ R` has card
    `τ_k(D)`: a support tuple with product `D` has all entries at
    most `D` (each entry is at most the product, since the other
    factors are at least 1), and conversely entries at most `D` with
    product `D` are automatically at most `R` and in the support. -/
theorem filter_tupleSupport_prod_eq {k R D : ℕ} (_hD1 : 1 ≤ D) (hDR : D ≤ R) :
    ((tupleSupport k R).filter (fun d => ∏ i, d i = D)).card
      = tupleProdCount k D := by
  have hset : (tupleSupport k R).filter (fun d => ∏ i, d i = D)
      = (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
        (fun d => ∏ i, d i = D) := by
    ext d
    simp only [Finset.mem_filter, mem_tupleSupport, Fintype.mem_piFinset,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, -, -⟩, hprod⟩
      refine ⟨fun i => ⟨h1 i, ?_⟩, hprod⟩
      have hle : d i ≤ ∏ j, d j :=
        Finset.single_le_prod' (fun j _ => h1 j) (Finset.mem_univ i)
      rw [hprod] at hle
      exact hle
    · rintro ⟨h1D, hprod⟩
      refine ⟨⟨fun i => (h1D i).1, fun i => le_trans (h1D i).2 hDR, ?_⟩, hprod⟩
      rw [hprod]
      exact hDR
  rw [hset, tupleProdCount]


/-- Exact fiberwise identity: the `ℓ¹` mass of the Selberg weight over
    the support equals the divisor-weighted sum over products. -/
theorem sum_abs_lamSelberg_eq {k R deg : ℕ} :
    ∑ d ∈ tupleSupport k R, |lamSelberg k R deg d|
      = ∑ D ∈ Finset.Icc 1 R,
        (tupleProdCount k D : ℝ)
          * |(ArithmeticFunction.moebius D : ℝ)
            * (1 - Real.log D / Real.log R) ^ deg| := by
  have hmaps : ∀ d ∈ tupleSupport k R, ∏ i, d i ∈ Finset.Icc 1 R := by
    intro d hd
    obtain ⟨h1, -, h3⟩ := mem_tupleSupport.mp hd
    rw [Finset.mem_Icc]
    exact ⟨Finset.one_le_prod' (fun i _ => h1 i), h3⟩
  have hinner : ∀ D ∈ Finset.Icc 1 R,
      (∑ d ∈ (tupleSupport k R).filter (fun d => ∏ i, d i = D),
        |lamSelberg k R deg d|)
        = (tupleProdCount k D : ℝ)
          * |(ArithmeticFunction.moebius D : ℝ)
            * (1 - Real.log D / Real.log R) ^ deg| := by
    intro D hD
    rw [Finset.mem_Icc] at hD
    have hterm : ∀ d ∈ (tupleSupport k R).filter (fun d => ∏ i, d i = D),
        |lamSelberg k R deg d|
          = |(ArithmeticFunction.moebius D : ℝ)
            * (1 - Real.log D / Real.log R) ^ deg| := by
      intro d hd
      rw [Finset.mem_filter] at hd
      rw [lamSelberg_eq_of_mem_support hd.1, hd.2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      filter_tupleSupport_prod_eq hD.1 hD.2]
  calc ∑ d ∈ tupleSupport k R, |lamSelberg k R deg d|
      = ∑ D ∈ Finset.Icc 1 R,
          ∑ d ∈ (tupleSupport k R).filter (fun d => ∏ i, d i = D),
            |lamSelberg k R deg d| :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ D ∈ Finset.Icc 1 R,
          (tupleProdCount k D : ℝ)
            * |(ArithmeticFunction.moebius D : ℝ)
              * (1 - Real.log D / Real.log R) ^ deg| :=
        Finset.sum_congr rfl hinner

/-! ### The τ-weighted λ-mass -/


/-- The λ-mass factors as the square of the `ℓ¹` mass. -/
theorem lambdaMass_eq_sq {k R deg : ℕ} :
    (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
      |lamSelberg k R deg d * lamSelberg k R deg e|)
      = (∑ d ∈ tupleSupport k R, |lamSelberg k R deg d|) ^ 2 := by
  have hstep : (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        |lamSelberg k R deg d * lamSelberg k R deg e|)
      = (∑ d ∈ tupleSupport k R, |lamSelberg k R deg d|)
        * (∑ e ∈ tupleSupport k R, |lamSelberg k R deg e|) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    rw [abs_mul]
  rw [hstep, pow_two]


/-- The τ-weighted λ-mass identity: `Λ` equals the square of the
    divisor-weighted sum. This is the sharp form of the mass bound:
    the squarefree restriction (via `μ`) and the polynomial decay
    (via the cutoff factor) stay visible, instead of being thrown
    away into the crude `|support|²` bound. -/
theorem lambdaMass_lamSelberg_eq {k R deg : ℕ} :
    (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
      |lamSelberg k R deg d * lamSelberg k R deg e|)
      = (∑ D ∈ Finset.Icc 1 R,
        (tupleProdCount k D : ℝ)
          * |(ArithmeticFunction.moebius D : ℝ)
            * (1 - Real.log D / Real.log R) ^ deg|) ^ 2 := by
  rw [lambdaMass_eq_sq, sum_abs_lamSelberg_eq]


/-- The one-line analytic input: `1/(d+1) ≤ log(d+1) - log d`, from
    `log x ≤ x - 1` applied to `x = d/(d+1)`. -/
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

/-! ### The divisor double count -/


/-- Multiples count: the multiples of `d` in `Icc 1 R` are exactly
    `R/d` in number, via `D = d * m` with `m ≤ R/d`. -/
theorem card_multiples_Icc {d R : ℕ} (hd : 1 ≤ d) :
    ((Finset.Icc 1 R).filter (fun D => d ∣ D)).card = R / d := by
  have hdpos : 0 < d := by omega
  have himg : (Finset.Icc 1 R).filter (fun D => d ∣ D)
      = (Finset.Icc 1 (R / d)).image (fun m => d * m) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hD1, hDR⟩, hdiv⟩
      obtain ⟨m, rfl⟩ := hdiv
      refine ⟨m, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos m with hm | hm
        · rw [hm] at hD1; simp at hD1
        · exact hm
      · exact (Nat.le_div_iff_mul_le hdpos).mpr (by rwa [mul_comm])
    · rintro ⟨m, ⟨hm1, hmR⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · have h := (Nat.le_div_iff_mul_le hdpos).mp hmR
        rwa [mul_comm] at h
  have hinj : Set.InjOn (fun m => d * m) (Finset.Icc 1 (R / d)) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hdpos hab
  rw [himg, Finset.card_image_of_injOn hinj, Nat.card_Icc]
  simp


/-- The divisor double count: `∑_{D ≤ R} τ(D) = ∑_{d ≤ R} R/d`. -/
theorem sum_divisors_card_eq (R : ℕ) :
    ∑ D ∈ Finset.Icc 1 R, (Nat.divisors D).card = ∑ d ∈ Finset.Icc 1 R, R / d := by
  have hpair : ∀ D ∈ Finset.Icc 1 R, (Nat.divisors D).card
      = ((Finset.Icc 1 R).filter (fun d => d ∣ D)).card := by
    intro D hD
    rw [Finset.mem_Icc] at hD
    congr 1
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdiv, hD0⟩
      have hd1 : 1 ≤ d := by
        rcases Nat.eq_zero_or_pos d with hd0 | hdpos
        · rw [hd0] at hdiv
          have hD00 : D = 0 := by simpa using hdiv
          exact (hD0 hD00).elim
        · exact hdpos
      exact ⟨⟨hd1, le_trans (Nat.le_of_dvd (by omega : 0 < D) hdiv) hD.2⟩, hdiv⟩
    · rintro ⟨⟨_, _⟩, hdiv⟩
      exact ⟨hdiv, by omega⟩
  rw [Finset.sum_congr rfl hpair]
  have h1 : ∀ D ∈ Finset.Icc 1 R, ((Finset.Icc 1 R).filter (fun d => d ∣ D)).card
      = ∑ d ∈ Finset.Icc 1 R, (if d ∣ D then (1 : ℕ) else 0) := by
    intro D _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Icc] at hd
  rw [Finset.sum_boole]
  exact card_multiples_Icc hd.1


/-- Hence `∑_{D ≤ R} τ(D) ≤ R * (1 + log R)`. -/
theorem sum_tau_le {R : ℕ} (hR : 1 ≤ R) :
    (∑ D ∈ Finset.Icc 1 R, ((Nat.divisors D).card : ℝ)) ≤
      (R : ℝ) * (1 + Real.log (R : ℝ)) := by
  calc (∑ D ∈ Finset.Icc 1 R, ((Nat.divisors D).card : ℝ))
      = ((∑ D ∈ Finset.Icc 1 R, (Nat.divisors D).card : ℕ) : ℝ) := by
        push_cast
        rfl
    _ = ((∑ d ∈ Finset.Icc 1 R, R / d : ℕ) : ℝ) := by rw [sum_divisors_card_eq]
    _ = ∑ d ∈ Finset.Icc 1 R, ((R / d : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∑ d ∈ Finset.Icc 1 R, (R : ℝ) / (d : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        exact Nat.cast_div_le
    _ = (R : ℝ) * ∑ d ∈ Finset.Icc 1 R, (1 : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [mul_one_div]
    _ ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (sum_Icc_inv_le hR) (by positivity)

/-! ### The divisor convolution identity for `τ_k` -/


/-- The `k`-fold divisor function satisfies the convolution identity
    `τ_{k+1}(D) = ∑_{e ∣ D} τ_k(D/e)`: split a `(k+1)`-tuple at its
    first coordinate. -/
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

/-! ### The divisor reindexing and the general `τ_k` bound -/


/-- Reindexing: summing `f(D/e)` over `e ∣ D`, `D ≤ R`, is the same
    as summing `f(m)` over `m ≤ R/e`, `e ≤ R`. -/
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


/-- The general bound `∑_{D ≤ R} τ_{k+1}(D) ≤ R * (1 + log R)^k`. -/
theorem sum_tupleProdCount_le : ∀ (k : ℕ) {R : ℕ}, 1 ≤ R →
    ∑ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1) D : ℝ) ≤
      (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k := by
  intro k
  induction k with
  | zero =>
    intro R hR
    show ∑ D ∈ Finset.Icc 1 R, (tupleProdCount 1 D : ℝ) ≤
      (R : ℝ) * (1 + Real.log (R : ℝ)) ^ 0
    have h1 : ∀ D ∈ Finset.Icc 1 R, (tupleProdCount 1 D : ℝ) = 1 := by
      intro D hD
      rw [Finset.mem_Icc] at hD
      have hset : (Fintype.piFinset (fun _ : Fin 1 => Finset.Icc 1 D)).filter
          (fun d => ∏ i, d i = D) = {fun _ => D} := by
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
            exact Finset.mem_Icc.mpr ⟨hD.1, le_rfl⟩
          · rw [Fin.prod_univ_one]
      have hcard : tupleProdCount 1 D = 1 := by
        simp only [tupleProdCount]
        rw [hset, Finset.card_singleton]
      rw [hcard, Nat.cast_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Nat.card_Icc]
    simp [pow_zero]
  | succ k ih =>
    intro R hR
    have hLHS : ∑ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1 + 1) D : ℝ)
        = ∑ e ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / e),
          (tupleProdCount (k + 1) m : ℝ) := by
      have h1 : ∀ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1 + 1) D : ℝ)
          = ∑ e ∈ Nat.divisors D, (tupleProdCount (k + 1) (D / e) : ℝ) := by
        intro D _
        rw [tupleProdCount_succ, Nat.cast_sum]
      rw [Finset.sum_congr rfl h1]
      exact sum_divisors_reindex (fun m => (tupleProdCount (k + 1) m : ℝ)) R
    rw [hLHS]
    have hbound : ∀ e ∈ Finset.Icc 1 R,
        ∑ m ∈ Finset.Icc 1 (R / e), (tupleProdCount (k + 1) m : ℝ)
          ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k * (1 / (e : ℝ)) := by
      intro e he
      rw [Finset.mem_Icc] at he
      by_cases h0 : R / e = 0
      · rw [h0]
        have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro m hm
          rw [Finset.mem_Icc] at hm
          omega
        rw [hempty, Finset.sum_empty]
        positivity
      · have h1 : 1 ≤ R / e := Nat.one_le_iff_ne_zero.mpr h0
        have ih' := ih h1
        have hcast : ((R / e : ℕ) : ℝ) ≤ (R : ℝ) / (e : ℝ) := Nat.cast_div_le
        have hlog : Real.log ((R / e : ℕ) : ℝ) ≤ Real.log (R : ℝ) := by
          by_cases hpos : (0 : ℝ) < ((R / e : ℕ) : ℝ)
          · exact Real.log_le_log hpos (by exact_mod_cast Nat.div_le_self R e)
          · have hz : ((R / e : ℕ) : ℝ) = 0 :=
              le_antisymm (le_of_not_gt hpos) (by positivity)
            rw [hz, Real.log_zero]
            exact Real.log_nonneg (by exact_mod_cast hR)
        have hnn1 : (0 : ℝ) ≤ 1 + Real.log ((R / e : ℕ) : ℝ) := by
          have hlognn : (0 : ℝ) ≤ Real.log ((R / e : ℕ) : ℝ) :=
            Real.log_nonneg (by exact_mod_cast h1)
          linarith
        have hpow : (1 + Real.log ((R / e : ℕ) : ℝ)) ^ k ≤
            (1 + Real.log (R : ℝ)) ^ k :=
          pow_le_pow_left₀ hnn1 (by linarith) k
        calc ∑ m ∈ Finset.Icc 1 (R / e), (tupleProdCount (k + 1) m : ℝ)
            ≤ ((R / e : ℕ) : ℝ) * (1 + Real.log ((R / e : ℕ) : ℝ)) ^ k := ih'
          _ ≤ ((R : ℝ) / (e : ℝ)) * (1 + Real.log (R : ℝ)) ^ k :=
              mul_le_mul hcast hpow (pow_nonneg hnn1 k) (by positivity)
          _ = (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k * (1 / (e : ℝ)) := by ring
    calc ∑ e ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / e), (tupleProdCount (k + 1) m : ℝ)
        ≤ ∑ e ∈ Finset.Icc 1 R, (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k * (1 / (e : ℝ)) :=
          Finset.sum_le_sum hbound
      _ = (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k * ∑ e ∈ Finset.Icc 1 R, (1 : ℝ) / (e : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k * (1 + Real.log (R : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Icc_inv_le hR) (by positivity)
      _ = (R : ℝ) * (1 + Real.log (R : ℝ)) ^ (k + 1) := by
          rw [pow_succ]; ring

/-! ### The Selberg λ-mass bound -/


/-- The divisor-weighted Selberg mass sum is at most `R * (1 + log R)^k`:
    each term is at most `τ_{k+1}(D)`, since `|μ| ≤ 1` and the cutoff
    factor lies in `[0,1]` on the range. -/
theorem selbergMassSum_le {k R deg : ℕ} (hR : 2 ≤ R) :
    ∑ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1) D : ℝ)
      * |(ArithmeticFunction.moebius D : ℝ)
        * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg|
      ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k := by
  calc ∑ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1) D : ℝ)
        * |(ArithmeticFunction.moebius D : ℝ)
          * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg|
      ≤ ∑ D ∈ Finset.Icc 1 R, (tupleProdCount (k + 1) D : ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        rw [Finset.mem_Icc] at hD
        have hlogR : (0 : ℝ) < Real.log (R : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < R by omega))
        have hlogD_nn : (0 : ℝ) ≤ Real.log (D : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hD.1)
        have hlogD_le : Real.log (D : ℝ) ≤ Real.log (R : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < D))
            (by exact_mod_cast hD.2)
        have hfrac_nn : (0 : ℝ) ≤ Real.log (D : ℝ) / Real.log (R : ℝ) :=
          div_nonneg hlogD_nn hlogR.le
        have hfrac_le : Real.log (D : ℝ) / Real.log (R : ℝ) ≤ 1 :=
          (div_le_one hlogR).mpr hlogD_le
        have hfac_nn : (0 : ℝ) ≤ 1 - Real.log (D : ℝ) / Real.log (R : ℝ) := by
          linarith
        have hfac_le : 1 - Real.log (D : ℝ) / Real.log (R : ℝ) ≤ 1 := by linarith
        have hpow_nn : (0 : ℝ) ≤
            (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg :=
          pow_nonneg hfac_nn _
        have hpow_le : (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg ≤ 1 :=
          pow_le_one₀ hfac_nn hfac_le
        have hmu : |(ArithmeticFunction.moebius D : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hfac : |(ArithmeticFunction.moebius D : ℝ)
            * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg hpow_nn]
          calc |(ArithmeticFunction.moebius D : ℝ)|
                * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg
              ≤ 1 * 1 := mul_le_mul hmu hpow_le hpow_nn zero_le_one
            _ = 1 := one_mul 1
        calc (tupleProdCount (k + 1) D : ℝ)
              * |(ArithmeticFunction.moebius D : ℝ)
                * (1 - Real.log (D : ℝ) / Real.log (R : ℝ)) ^ deg|
            ≤ (tupleProdCount (k + 1) D : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hfac (by positivity)
          _ = (tupleProdCount (k + 1) D : ℝ) := mul_one _
    _ ≤ (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k :=
        sum_tupleProdCount_le k (by omega)


/-- The Selberg λ-mass with the crude `|support|²` bound replaced by
    the τ-weighted polylog bound: `Λ ≤ (R * (1 + log R)^k)²` for tuple
    size `k+1`. Compare the crude bound `Λ ≤ |support|² ≤ R^{2k+2}`:
    this saves a factor of roughly `R^{2k}` against the crude bound. -/
theorem lambdaMass_lamSelberg_le_tau {k R deg : ℕ} (hR : 2 ≤ R) :
    (∑ d ∈ tupleSupport (k + 1) R, ∑ e ∈ tupleSupport (k + 1) R,
      |lamSelberg (k + 1) R deg d * lamSelberg (k + 1) R deg e|)
      ≤ ((R : ℝ) * (1 + Real.log (R : ℝ)) ^ k) ^ 2 := by
  rw [lambdaMass_lamSelberg_eq]
  exact pow_le_pow_left₀ (by positivity) (selbergMassSum_le hR) 2


end GPY

theorem solution {R : ℕ} (hR : 1 ≤ R) :
    (∑ D ∈ Finset.Icc 1 R, ((Nat.divisors D).card : ℝ)) ≤
      (R : ℝ) * (1 + Real.log (R : ℝ)) := GPY.sum_tau_le hR
