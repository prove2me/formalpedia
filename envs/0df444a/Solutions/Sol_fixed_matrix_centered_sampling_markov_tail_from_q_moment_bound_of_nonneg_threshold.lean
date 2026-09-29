-- Prove2me | solution 1 for fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T13:50:51.242013+00:00
-- url     : https://prove2.me/submissions/ed60fd76-5266-451a-b56a-a759a2ea83e0

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

private lemma bernoulliObservationWeight_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp _)
    (pow_nonneg (sub_nonneg.mpr hp_one) _)

private lemma sum_bernoulliObservationWeight_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} (_hp : 0 ≤ p) (_hp_one : p ≤ 1) :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega) = 1 := by
  classical
  let α := Fin n₁ × Fin n₂
  let N := Fintype.card α
  have hsum_powerset :
      (∑ Omega : Finset α,
          p ^ Omega.card * (1 - p) ^ (N - Omega.card)) =
        ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [← Finset.powerset_univ]
    rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k hk
    have hcard :
        (Finset.univ : Finset α).card = N := by
      simp [N]
    have h :=
      Finset.sum_powersetCard k (Finset.univ : Finset α)
        (fun j : ℕ => p ^ j * (1 - p) ^ (N - j))
    simpa [hcard, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega)
        = ∑ Omega : Finset α,
            p ^ Omega.card * (1 - p) ^ (N - Omega.card) := by
          simp [α, N, bernoulliObservationWeight]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := hsum_powerset
    _ = ∑ k ∈ Finset.range (N + 1),
          p ^ k * (1 - p) ^ (N - k) * (Nat.choose N k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (p + (1 - p)) ^ N := by
          rw [add_pow]
    _ = 1 := by
          ring

private lemma spectralNorm_nonneg {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    0 ≤ spectralNorm X := by
  unfold spectralNorm
  exact norm_nonneg _

private lemma bernoulliEventProb_add_compl
    {n₁ n₂ : ℕ} {p : ℝ} (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p Event +
        (∑ Omega : Finset (Fin n₁ × Fin n₂),
          if Event Omega then 0 else bernoulliObservationWeight p Omega) =
      ∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega := by
  classical
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Omega _
  by_cases hEvent : Event Omega
  · simp [hEvent]
  · simp [hEvent]

private lemma bernoulliExpectation_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) (hF : ∀ Omega, 0 ≤ F Omega) :
    0 ≤ bernoulliExpectation p F := by
  unfold bernoulliExpectation
  apply Finset.sum_nonneg
  intro Omega _
  exact mul_nonneg (bernoulliObservationWeight_nonneg hp hp_one Omega) (hF Omega)

private lemma bad_weight_mul_threshold_pow_le_expectation
    {n₁ n₂ : ℕ} {p threshold : ℝ} {q : ℕ}
    (hp : 0 ≤ p) (hp_one : p ≤ 1) (hthreshold : 0 ≤ threshold)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) (hF : ∀ Omega, 0 ≤ F Omega) :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        if F Omega ≤ threshold then 0 else bernoulliObservationWeight p Omega) *
        threshold ^ q ≤
      bernoulliExpectation p (fun Omega => F Omega ^ q) := by
  classical
  unfold bernoulliExpectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro Omega _
  by_cases hGood : F Omega ≤ threshold
  · simp [hGood]
    exact mul_nonneg (bernoulliObservationWeight_nonneg hp hp_one Omega)
      (pow_nonneg (hF Omega) q)
  · have hle : threshold ^ q ≤ F Omega ^ q := by
      exact pow_le_pow_left₀ hthreshold (le_of_not_ge hGood) q
    have hw : 0 ≤ bernoulliObservationWeight p Omega :=
      bernoulliObservationWeight_nonneg hp hp_one Omega
    simpa [hGood, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hle hw

private lemma bad_probability_eq_zero_of_zero_threshold
    {n₁ n₂ : ℕ} {p : ℝ} {q : ℕ}
    (hp : 0 ≤ p) (hp_one : p ≤ 1) (hq : 1 ≤ q)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) (hF : ∀ Omega, 0 ≤ F Omega)
    (hExp :
      bernoulliExpectation p (fun Omega => F Omega ^ q) = 0) :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        if F Omega ≤ 0 then 0 else bernoulliObservationWeight p Omega) = 0 := by
  classical
  have hq_pos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hterm_zero :
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega * F Omega ^ q = 0 := by
    have hsum :
        (∑ Omega : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Omega * F Omega ^ q) = 0 := by
      simpa [bernoulliExpectation] using hExp
    have hnonneg :
        ∀ Omega ∈ (Finset.univ : Finset (Finset (Fin n₁ × Fin n₂))),
          0 ≤ bernoulliObservationWeight p Omega * F Omega ^ q := by
      intro Omega _
      exact mul_nonneg (bernoulliObservationWeight_nonneg hp hp_one Omega)
        (pow_nonneg (hF Omega) q)
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp (by
        simpa using hsum)
    intro Omega
    exact hzero Omega (by simp)
  apply Finset.sum_eq_zero
  intro Omega _
  by_cases hGood : F Omega ≤ 0
  · simp [hGood]
  · have hF_pos : 0 < F Omega := lt_of_not_ge hGood
    have hpow_pos : 0 < F Omega ^ q := pow_pos hF_pos q
    have hw_zero : bernoulliObservationWeight p Omega = 0 := by
      have hz := hterm_zero Omega
      rcases mul_eq_zero.mp hz with hw | hpow
      · exact hw
      · exact False.elim ((ne_of_gt hpow_pos) hpow)
    simp [hGood, hw_zero]

theorem solution :
    ∀ (β threshold : ℝ), 2 < β → 0 ≤ threshold →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          threshold ^ q * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X threshold) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro β threshold hβ hthreshold n₁ n₂ m q X hn₁ hn₂ hm hq hMoment
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let F : Finset (Fin n₁ × Fin n₂) → ℝ := fun Omega =>
    spectralNorm (centeredSamplingFluctuation Omega p X)
  let Good : Finset (Fin n₁ × Fin n₂) → Prop := fun Omega =>
    F Omega ≤ threshold
  let badProb : ℝ :=
    ∑ Omega : Finset (Fin n₁ × Fin n₂),
      if Good Omega then 0 else bernoulliObservationWeight p Omega
  let tail : ℝ := Real.rpow (↑(max n₁ n₂)) (-β)
  have hp_bounds := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hp : 0 ≤ p := by
    simpa [p] using hp_bounds.1
  have hp_one : p ≤ 1 := by
    simpa [p] using hp_bounds.2
  have hF_nonneg : ∀ Omega, 0 ≤ F Omega := by
    intro Omega
    exact spectralNorm_nonneg _
  have hMomentF :
      bernoulliExpectation p (fun Omega => F Omega ^ q) ≤
        threshold ^ q * tail := by
    simpa [p, F, tail] using hMoment
  have hmax_pos_nat : 0 < max n₁ n₂ := by
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have htail_nonneg : 0 ≤ tail := by
    exact Real.rpow_nonneg (Nat.cast_nonneg _) (-β)
  have hprob_add :
      bernoulliEventProb p Good + badProb = 1 := by
    have h :=
      bernoulliEventProb_add_compl (p := p) (n₁ := n₁) (n₂ := n₂) Good
    simpa [badProb, sum_bernoulliObservationWeight_eq_one hp hp_one] using h
  have hbad_le_tail : badProb ≤ tail := by
    by_cases hthreshold_pos : 0 < threshold
    · have hbad_mul_le :
          badProb * threshold ^ q ≤
            bernoulliExpectation p (fun Omega => F Omega ^ q) := by
        simpa [badProb, Good] using
          bad_weight_mul_threshold_pow_le_expectation
            (p := p) (threshold := threshold) (q := q)
            hp hp_one hthreshold F hF_nonneg
      have hmul_le : badProb * threshold ^ q ≤ tail * threshold ^ q := by
        have h := le_trans hbad_mul_le hMomentF
        simpa [mul_comm, mul_left_comm, mul_assoc] using h
      exact le_of_mul_le_mul_right hmul_le (pow_pos hthreshold_pos q)
    · have hthreshold_eq : threshold = 0 := by
        exact le_antisymm (le_of_not_gt hthreshold_pos) hthreshold
      have hq_pos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
      have hthreshold_pow_zero : threshold ^ q = 0 := by
        subst threshold
        cases q with
        | zero =>
            omega
        | succ q =>
            simp
      have hExp_nonneg :
          0 ≤ bernoulliExpectation p (fun Omega => F Omega ^ q) :=
        bernoulliExpectation_nonneg hp hp_one (fun Omega => F Omega ^ q)
          (fun Omega => pow_nonneg (hF_nonneg Omega) q)
      have hExp_le_zero :
          bernoulliExpectation p (fun Omega => F Omega ^ q) ≤ 0 := by
        simpa [hthreshold_pow_zero] using hMomentF
      have hExp_eq_zero :
          bernoulliExpectation p (fun Omega => F Omega ^ q) = 0 :=
        le_antisymm hExp_le_zero hExp_nonneg
      have hbad_zero :
          badProb = 0 := by
        have hzero :=
          bad_probability_eq_zero_of_zero_threshold
            (p := p) (q := q) hp hp_one hq F hF_nonneg hExp_eq_zero
        simpa [badProb, Good, hthreshold_eq] using hzero
      simpa [hbad_zero] using htail_nonneg
  have hgood :
      bernoulliEventProb p Good ≥ 1 - tail := by
    linarith
  simpa [p, F, Good, CenteredSamplingSpectralBound, tail, one_mul] using hgood
