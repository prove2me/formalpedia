-- Prove2me | solution 1 for talagrand_bernoulli_sSup_log_tail_from_finite_max
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-29T17:30:03.352091+00:00
-- url     : https://prove2.me/submissions/a660322f-5033-4279-b985-a5f93665f81e

import Definitions.Def_matrix_completion_bernoulli
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_bernoulli_event_prob_nonneg
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
    {n₁ n₂ : ℕ} {p : ℝ} :
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

private lemma bernoulliEventProb_true
    {n₁ n₂ : ℕ} {p : ℝ} :
    bernoulliEventProb p (fun _ : Finset (Fin n₁ × Fin n₂) => True) = 1 := by
  unfold bernoulliEventProb
  simpa using sum_bernoulliObservationWeight_eq_one (n₁ := n₁) (n₂ := n₂) (p := p)

private lemma bernoulliExpectation_zero
    {n₁ n₂ : ℕ} {p : ℝ} :
    bernoulliExpectation p (fun _ : Finset (Fin n₁ × Fin n₂) => (0 : ℝ)) = 0 := by
  unfold bernoulliExpectation
  simp

private lemma centeredIndicatorSub_abs_le_one
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    |(if b then (1 : ℝ) else 0) - p| ≤ 1 := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_sub]
    simpa [abs_of_nonneg hp0, abs_neg] using hp1
  · simp only [↓reduceIte]
    have hnonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    have hle : 1 - p ≤ 1 := by linarith
    simpa [abs_of_nonneg hnonneg] using hle

private lemma centeredProcess_sum_le_bound
    {n₁ n₂ : ℕ} {p B : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (coeff : Fin n₁ → Fin n₂ → ℝ)
    (hcoeff : ∀ i j, |coeff i j| ≤ B)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    (∑ i : Fin n₁, ∑ j : Fin n₂,
      (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) * coeff i j)) ≤
      ((n₁ : ℝ) * (n₂ : ℝ)) * B := by
  have hterm : ∀ i : Fin n₁, ∀ j : Fin n₂,
      (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) * coeff i j) ≤ B := by
    intro i j
    have hf : |(if (i, j) ∈ Omega then (1 : ℝ) else 0) - p| ≤ 1 := by
      by_cases hmem : (i, j) ∈ Omega
      · simpa [hmem] using centeredIndicatorSub_abs_le_one hp0 hp1 true
      · simpa [hmem] using centeredIndicatorSub_abs_le_one hp0 hp1 false
    calc
      (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) * coeff i j)
          ≤ |(((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) * coeff i j)| :=
            le_abs_self _
      _ = |((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p)| * |coeff i j| := by
            rw [abs_mul]
      _ ≤ 1 * B := mul_le_mul hf (hcoeff i j) (abs_nonneg _) (by norm_num)
      _ = B := by ring
  calc
    (∑ i : Fin n₁, ∑ j : Fin n₂,
      (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) * coeff i j))
      ≤ ∑ i : Fin n₁, ∑ j : Fin n₂, B := by
        exact Finset.sum_le_sum
          (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = ((n₁ : ℝ) * (n₂ : ℝ)) * B := by
        simp [Finset.sum_const, mul_left_comm, mul_comm]

private lemma centeredProcess_candidates_bddAbove
    {n₁ n₂ : ℕ} {p B : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type} (coeff : ι → Fin n₁ → Fin n₂ → ℝ)
    (hcoeff : ∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂, |coeff a i j| ≤ B)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    BddAbove {v : ℝ |
      ∃ a : ι,
        v =
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
              coeff a i j)} := by
  refine ⟨((n₁ : ℝ) * (n₂ : ℝ)) * B, ?_⟩
  rintro v ⟨a, rfl⟩
  exact centeredProcess_sum_le_bound hp0 hp1 (coeff a) (hcoeff a) Omega

private lemma centeredProcess_sSup_nonneg
    {n₁ n₂ : ℕ} {p B : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type} (hι : Nonempty ι)
    (coeff : ι → Fin n₁ → Fin n₂ → ℝ)
    (hsym : ∀ a : ι, ∃ a' : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
      coeff a' i j = -coeff a i j)
    (hcoeff : ∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂, |coeff a i j| ≤ B)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ sSup {v : ℝ |
      ∃ a : ι,
        v =
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
              coeff a i j)} := by
  let S : Set ℝ := {v : ℝ |
      ∃ a : ι,
        v =
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
              coeff a i j)}
  have hbdd : BddAbove S := by
    simpa [S] using centeredProcess_candidates_bddAbove hp0 hp1 coeff hcoeff Omega
  rcases hι with ⟨a⟩
  rcases hsym a with ⟨a', ha'⟩
  let x : ℝ :=
    ∑ i : Fin n₁, ∑ j : Fin n₂,
      (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) * coeff a i j)
  have hxmem : x ∈ S := by
    exact ⟨a, rfl⟩
  have hx'mem : -x ∈ S := by
    refine ⟨a', ?_⟩
    dsimp [x]
    simp [ha']
  by_cases hx : 0 ≤ x
  · exact hx.trans (le_csSup hbdd hxmem)
  · have hnx : 0 ≤ -x := by linarith
    exact hnx.trans (le_csSup hbdd hx'mem)

private lemma bernoulliExpectation_mono
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    {F G : Finset (Fin n₁ × Fin n₂) → ℝ}
    (hFG : ∀ Omega, F Omega ≤ G Omega) :
    bernoulliExpectation p F ≤ bernoulliExpectation p G := by
  unfold bernoulliExpectation
  exact Finset.sum_le_sum (fun Omega _ =>
    mul_le_mul_of_nonneg_left (hFG Omega)
      (bernoulliObservationWeight_nonneg hp hp_one Omega))

private lemma bernoulliExpectation_nonneg
    {n₁ n₂ : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    {F : Finset (Fin n₁ × Fin n₂) → ℝ}
    (hF : ∀ Omega, 0 ≤ F Omega) :
    0 ≤ bernoulliExpectation p F := by
  unfold bernoulliExpectation
  exact Finset.sum_nonneg (fun Omega _ =>
    mul_nonneg (bernoulliObservationWeight_nonneg hp hp_one Omega) (hF Omega))

private lemma bernoulliExpectation_le_add_const
    {n₁ n₂ : ℕ} {p δ : ℝ} (hp : 0 ≤ p) (hp_one : p ≤ 1)
    {F G : Finset (Fin n₁ × Fin n₂) → ℝ}
    (hFG : ∀ Omega, F Omega ≤ G Omega + δ) :
    bernoulliExpectation p F ≤ bernoulliExpectation p G + δ := by
  unfold bernoulliExpectation
  have hsum :
      (∑ Omega : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega * F Omega) ≤
        ∑ Omega : Finset (Fin n₁ × Fin n₂),
          bernoulliObservationWeight p Omega * (G Omega + δ) := by
    exact Finset.sum_le_sum (fun Omega _ =>
      mul_le_mul_of_nonneg_left (hFG Omega)
        (bernoulliObservationWeight_nonneg hp hp_one Omega))
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega * F Omega)
        ≤ ∑ Omega : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Omega * (G Omega + δ) := hsum
    _ = (∑ Omega : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Omega * G Omega) +
          δ * ∑ Omega : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Omega := by
          calc
            (∑ Omega : Finset (Fin n₁ × Fin n₂),
                bernoulliObservationWeight p Omega * (G Omega + δ))
                =
              ∑ Omega : Finset (Fin n₁ × Fin n₂),
                (bernoulliObservationWeight p Omega * G Omega +
                  δ * bernoulliObservationWeight p Omega) := by
                apply Finset.sum_congr rfl
                intro Omega _
                ring
            _ =
              (∑ Omega : Finset (Fin n₁ × Fin n₂),
                bernoulliObservationWeight p Omega * G Omega) +
              ∑ Omega : Finset (Fin n₁ × Fin n₂),
                δ * bernoulliObservationWeight p Omega := by
                rw [Finset.sum_add_distrib]
            _ =
              (∑ Omega : Finset (Fin n₁ × Fin n₂),
                bernoulliObservationWeight p Omega * G Omega) +
              δ * ∑ Omega : Finset (Fin n₁ × Fin n₂),
                bernoulliObservationWeight p Omega := by
                rw [Finset.mul_sum]
    _ = (∑ Omega : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p Omega * G Omega) + δ := by
          rw [sum_bernoulliObservationWeight_eq_one]
          ring

private lemma log_one_add_half_twice_ge {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ 2 * Real.log (1 + x / 2) := by
  have hpos1 : 0 < 1 + x := by linarith
  have hsq : 1 + x ≤ (1 + x / 2) ^ 2 := by
    nlinarith [sq_nonneg (x / 2)]
  have hlog := Real.log_le_log hpos1 hsq
  have hrewrite : Real.log ((1 + x / 2) ^ 2) = 2 * Real.log (1 + x / 2) := by
    simpa using Real.log_pow (1 + x / 2) 2
  simpa [hrewrite] using hlog

private lemma talagrand_log_tail_half_radius_le_four_constant
    {K B t D Dθ : ℝ} (hK : 0 < K) (hB : 0 < B) (ht : 0 < t)
    (hD : 0 < D) (hDθ : 0 < Dθ) (hDθle : Dθ ≤ D) :
    3 * Real.exp
        (-((t / 2) / (K * B)) *
          Real.log (1 + (B * (t / 2)) / Dθ)) ≤
      3 * Real.exp
        (-(t / ((4 * K) * B)) *
          Real.log (1 + (B * t) / D)) := by
  let x : ℝ := (B * t) / D
  have hx : 0 ≤ x := by positivity
  have hratio_ge : x / 2 ≤ (B * (t / 2)) / Dθ := by
    dsimp [x]
    have hnum_nonneg : 0 ≤ B * (t / 2) := by positivity
    have hrewrite : (B * t / D) / 2 = (B * (t / 2)) / D := by
      field_simp [hD.ne']
    rw [hrewrite]
    exact div_le_div_of_nonneg_left hnum_nonneg hDθ hDθle
  have hlog_ratio :
      Real.log (1 + x / 2) ≤
        Real.log (1 + (B * (t / 2)) / Dθ) := by
    have hpos : 0 < 1 + x / 2 := by positivity
    exact Real.log_le_log hpos (by linarith)
  have hlog_main :
      Real.log (1 + x) ≤
        2 * Real.log (1 + (B * (t / 2)) / Dθ) := by
    calc
      Real.log (1 + x) ≤ 2 * Real.log (1 + x / 2) :=
        log_one_add_half_twice_ge hx
      _ ≤ 2 * Real.log (1 + (B * (t / 2)) / Dθ) := by
        nlinarith [hlog_ratio]
  have hcoef_pos : 0 < t / ((4 * K) * B) := by positivity
  have hcoef_eq : (t / 2) / (K * B) = 2 * (t / ((4 * K) * B)) := by
    field_simp [hK.ne', hB.ne']
    ring
  have hprod :
      (t / ((4 * K) * B)) * Real.log (1 + (B * t) / D) ≤
        ((t / 2) / (K * B)) * Real.log (1 + (B * (t / 2)) / Dθ) := by
    have hmul := mul_le_mul_of_nonneg_left hlog_main hcoef_pos.le
    dsimp [x] at hmul
    rw [hcoef_eq]
    nlinarith
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  apply Real.exp_le_exp.mpr
  linarith

private lemma one_sub_nonpos_tail_le_one
    (K B sigmaSq t meanZ : ℝ) (hB : 0 < B) (hK : 0 < K) :
    1 -
        3 * Real.exp
          (-(t / (K * B)) *
            Real.log (1 + (B * t) / (sigmaSq + B * meanZ))) ≤ 1 := by
  have hexp_nonneg :
      0 ≤
        3 * Real.exp
          (-(t / (K * B)) *
            Real.log (1 + (B * t) / (sigmaSq + B * meanZ))) := by
    positivity
  linarith

private lemma tail_rhs_at_zero_le_event_prob
    {n₁ n₂ : ℕ} {p K B sigmaSq meanZ : ℝ}
    (Event : Finset (Fin n₁ × Fin n₂) → Prop)
    (hp : 0 ≤ p) (hp_one : p ≤ 1) :
    1 -
        3 * Real.exp
          (-((0 : ℝ) / (K * B)) *
            Real.log (1 + (B * 0) / (sigmaSq + B * meanZ))) ≤
      bernoulliEventProb p Event := by
  have hprob_nonneg : 0 ≤ bernoulliEventProb p Event :=
    bernoulli_event_prob_nonneg Event hp hp_one
  have htail :
      1 -
          3 * Real.exp
            (-((0 : ℝ) / (K * B)) *
              Real.log (1 + (B * 0) / (sigmaSq + B * meanZ))) = -2 := by
    norm_num
  linarith

theorem solution
    (hfinite :
      ∃ K : ℝ, 0 < K ∧
        ∀ (n₁ n₂ m : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
          (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
          0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
          0 < B → 0 ≤ sigmaSq → 0 ≤ t →
          (∀ a : ι, ∃ a' : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
            coeff a' i j = -coeff a i j) →
          (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
            |coeff a i j| ≤ B) →
          (∀ a : ι,
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  (coeff a i j) ^ 2 ≤ sigmaSq) →
          let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
          let Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
            fun Omega =>
              Finset.univ.sup' Finset.univ_nonempty
                (fun a : ι =>
                  ∑ i : Fin n₁, ∑ j : Fin n₂,
                    (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                      coeff a i j))
          bernoulliEventProb p
              (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t) ≥
            1 -
              3 * Real.exp
                (-(t / (K * B)) *
                  Real.log
                    (1 + (B * t) /
                      (sigmaSq + B * bernoulliExpectation p Z)))) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (n₁ n₂ m : ℕ) (ι : Type) (Z : Finset (Fin n₁ × Fin n₂) → ℝ)
        (coeff : ι → Fin n₁ → Fin n₂ → ℝ) (B sigmaSq t : ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ Omega,
          Z Omega =
            sSup {v : ℝ |
              ∃ a : ι,
                v =
                  ∑ i : Fin n₁, ∑ j : Fin n₂,
                    (((if (i, j) ∈ Omega then (1 : ℝ) else 0) -
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      coeff a i j)}) →
        (∀ a : ι, ∃ a' : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          coeff a' i j = -coeff a i j) →
        (∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          |coeff a i j| ≤ B) →
        (∀ a : ι,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (coeff a i j) ^ 2 ≤ sigmaSq) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Z Omega -
                  bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Z| ≤ t) ≥
          1 -
            3 * Real.exp
              (-(t / (K * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq +
                      B * bernoulliExpectation
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Z))) := by
  classical
  rcases hfinite with ⟨K, hK, hfiniteK⟩
  refine ⟨4 * K, by positivity, ?_⟩
  intro n₁ n₂ m ι Z coeff B sigmaSq t hn₁ hn₂ hm hB hsigma ht hZ hsym hcoeff hvar
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp_bounds := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  by_cases ht0 : t = 0
  · subst t
    exact tail_rhs_at_zero_le_event_prob
      (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        |Z Omega - bernoulliExpectation p Z| ≤ 0)
      hp_bounds.1 hp_bounds.2
  by_cases hι : Nonempty ι
  ·
    -- The nonempty, positive-radius case is the genuine approximation step:
    -- choose finitely many nearly extremizing indices, close them under
    -- symmetry, apply the finite-max theorem at radius `t/2`, and absorb the
    -- loss by replacing `K` with `4K`.
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hZ_nonneg : ∀ Omega, 0 ≤ Z Omega := by
      intro Omega
      have hnonneg :=
        centeredProcess_sSup_nonneg hp_bounds.1 hp_bounds.2 hι coeff hsym hcoeff Omega
      simpa [p, hZ Omega] using hnonneg
    have hEZ_nonneg : 0 ≤ bernoulliExpectation p Z :=
      bernoulliExpectation_nonneg hp_bounds.1 hp_bounds.2 hZ_nonneg
    let D : ℝ := sigmaSq + B * bernoulliExpectation p Z
    have hD_nonneg : 0 ≤ D := by
      dsimp [D]
      nlinarith [hsigma, hB.le, hEZ_nonneg]
    let δ : ℝ := if 0 < D then min (t / 4) (D / (4 * B)) else t / 4
    have ht_quarter_pos : 0 < t / 4 := by positivity
    have hδpos : 0 < δ := by
      by_cases hDpos : 0 < D
      · have hDdiv_pos : 0 < D / (4 * B) := by positivity
        simp [δ, hDpos, lt_min_iff, ht_quarter_pos, hDdiv_pos]
      · simp [δ, hDpos, ht_quarter_pos]
    have hδnonneg : 0 ≤ δ := hδpos.le
    have hδ_le_quarter : δ ≤ t / 4 := by
      by_cases hDpos : 0 < D
      · simp [δ, hDpos, min_le_left]
      · simp [δ, hDpos]
    have hδ_le_Ddiv (hDpos : 0 < D) : δ ≤ D / (4 * B) := by
      simp [δ, hDpos, min_le_right]
    have hApprox :
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
          ∃ a : ι,
            Z Omega - δ <
              ∑ i : Fin n₁, ∑ j : Fin n₂,
                (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                  coeff a i j) := by
      intro Omega
      let S : Set ℝ := {v : ℝ |
        ∃ a : ι,
          v =
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                coeff a i j)}
      have hSnonempty : S.Nonempty := by
        rcases hι with ⟨a⟩
        refine ⟨∑ i : Fin n₁, ∑ j : Fin n₂,
              (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                coeff a i j), ?_⟩
        exact ⟨a, rfl⟩
      have hlt : Z Omega - δ < sSup S := by
        have hz : Z Omega = sSup S := by
          simpa [S, p] using hZ Omega
        rw [hz]
        linarith
      rcases exists_lt_of_lt_csSup hSnonempty hlt with ⟨v, hv, hvlt⟩
      rcases hv with ⟨a, rfl⟩
      exact ⟨a, hvlt⟩
    let approx : Finset (Fin n₁ × Fin n₂) → ι :=
      fun Omega => Classical.choose (hApprox Omega)
    have hApprox_spec :
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
          Z Omega - δ <
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                coeff (approx Omega) i j) := by
      intro Omega
      simpa [approx] using Classical.choose_spec (hApprox Omega)
    let sym : ι → ι := fun a => Classical.choose (hsym a)
    have hsym_spec :
        ∀ a : ι, ∀ i : Fin n₁, ∀ j : Fin n₂,
          coeff (sym a) i j = -coeff a i j := by
      intro a i j
      simpa [sym] using Classical.choose_spec (hsym a) i j
    let θ : Type := Finset (Fin n₁ × Fin n₂) × Bool
    let idx : θ → ι := fun x => if x.2 then sym (approx x.1) else approx x.1
    let coeffθ : θ → Fin n₁ → Fin n₂ → ℝ := fun x i j => coeff (idx x) i j
    let Zθ : Finset (Fin n₁ × Fin n₂) → ℝ :=
      fun Omega =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun x : θ =>
            ∑ i : Fin n₁, ∑ j : Fin n₂,
              (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                coeffθ x i j))
    have hθsym :
        ∀ x : θ, ∃ x' : θ, ∀ i : Fin n₁, ∀ j : Fin n₂,
          coeffθ x' i j = -coeffθ x i j := by
      intro x
      refine ⟨(x.1, !x.2), ?_⟩
      intro i j
      cases x with
      | mk Omega b =>
          cases b
          · simp [coeffθ, idx, sym, hsym_spec]
          · simp [coeffθ, idx, sym, hsym_spec]
    have hθcoeff :
        ∀ x : θ, ∀ i : Fin n₁, ∀ j : Fin n₂, |coeffθ x i j| ≤ B := by
      intro x i j
      exact hcoeff (idx x) i j
    have hθvar :
        ∀ x : θ,
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            p * (1 - p) * (coeffθ x i j) ^ 2 ≤ sigmaSq := by
      intro x
      simpa [p, coeffθ, idx] using hvar (idx x)
    have ht_half_nonneg : 0 ≤ t / 2 := by positivity
    have hFiniteProb :
        bernoulliEventProb p
            (fun Omega => |Zθ Omega - bernoulliExpectation p Zθ| ≤ t / 2) ≥
          1 -
            3 * Real.exp
              (-((t / 2) / (K * B)) *
                Real.log
                  (1 + (B * (t / 2)) /
                    (sigmaSq + B * bernoulliExpectation p Zθ))) := by
      simpa [p, θ, coeffθ, Zθ] using
        hfiniteK n₁ n₂ m θ coeffθ B sigmaSq (t / 2)
          hn₁ hn₂ hm hB hsigma ht_half_nonneg hθsym hθcoeff hθvar
    have hZθ_le_Z : ∀ Omega, Zθ Omega ≤ Z Omega := by
      intro Omega
      unfold Zθ
      refine Finset.sup'_le Finset.univ_nonempty
        (fun x : θ =>
          ∑ i : Fin n₁, ∑ j : Fin n₂,
            (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
              coeffθ x i j)) ?_
      intro x hx
      have hmem :
          (∑ i : Fin n₁, ∑ j : Fin n₂,
            (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
              coeffθ x i j)) ∈
            ({v : ℝ |
              ∃ a : ι,
                v =
                  ∑ i : Fin n₁, ∑ j : Fin n₂,
                    (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                      coeff a i j)} : Set ℝ) := by
        exact ⟨idx x, by simp [coeffθ]⟩
      have hle :=
        le_csSup
          (centeredProcess_candidates_bddAbove hp_bounds.1 hp_bounds.2 coeff hcoeff Omega)
          hmem
      simpa [p, hZ Omega] using hle
    have hZ_le_Zθ_add : ∀ Omega, Z Omega ≤ Zθ Omega + δ := by
      intro Omega
      have hsel_le :
          (∑ i : Fin n₁, ∑ j : Fin n₂,
            (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
              coeff (approx Omega) i j)) ≤ Zθ Omega := by
        have hle :=
          Finset.le_sup'
            (s := (Finset.univ : Finset θ))
            (f := fun x : θ =>
              ∑ i : Fin n₁, ∑ j : Fin n₂,
                (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                  coeffθ x i j))
            (b := (Omega, false))
            (by simp)
        exact hle
      have happrox := hApprox_spec Omega
      linarith
    have hEZθ_le_EZ : bernoulliExpectation p Zθ ≤ bernoulliExpectation p Z :=
      bernoulliExpectation_mono hp_bounds.1 hp_bounds.2 hZθ_le_Z
    have hEZ_le_EZθ_add : bernoulliExpectation p Z ≤ bernoulliExpectation p Zθ + δ :=
      bernoulliExpectation_le_add_const hp_bounds.1 hp_bounds.2 hZ_le_Zθ_add
    have hdelta_absorb : t / 2 + δ ≤ t := by
      linarith
    have hGoodImp :
        ∀ Omega,
          |Zθ Omega - bernoulliExpectation p Zθ| ≤ t / 2 →
          |Z Omega - bernoulliExpectation p Z| ≤ t := by
      intro Omega hgood
      rw [abs_sub_le_iff] at hgood ⊢
      constructor
      · have hleft :
            Z Omega - bernoulliExpectation p Z ≤
              (Zθ Omega - bernoulliExpectation p Zθ) + δ := by
          linarith [hZ_le_Zθ_add Omega, hEZθ_le_EZ]
        linarith
      · have hright :
            bernoulliExpectation p Z - Z Omega ≤
              (bernoulliExpectation p Zθ - Zθ Omega) + δ := by
          linarith [hEZ_le_EZθ_add, hZθ_le_Z Omega]
        linarith
    have hProbTransfer :
        bernoulliEventProb p
            (fun Omega => |Zθ Omega - bernoulliExpectation p Zθ| ≤ t / 2) ≤
          bernoulliEventProb p
            (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t) :=
      bernoulli_event_probability_mono p _ _ hp_bounds.1 hp_bounds.2 hGoodImp
    have hTargetFromFinite :
        bernoulliEventProb p
            (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t) ≥
          1 -
            3 * Real.exp
              (-((t / 2) / (K * B)) *
                Real.log
                  (1 + (B * (t / 2)) /
                    (sigmaSq + B * bernoulliExpectation p Zθ))) := by
      linarith
    let Dθ : ℝ := sigmaSq + B * bernoulliExpectation p Zθ
    by_cases hDpos : 0 < D
    · have hDθleD : Dθ ≤ D := by
        dsimp [Dθ, D]
        have hmul := mul_le_mul_of_nonneg_left hEZθ_le_EZ hB.le
        linarith
      have hBδ_le : B * δ ≤ D / 4 := by
        have hδD := hδ_le_Ddiv hDpos
        have hmul := mul_le_mul_of_nonneg_left hδD hB.le
        have heq : B * (D / (4 * B)) = D / 4 := by
          field_simp [hB.ne']
        simpa [heq] using hmul
      have hD_le_Dθ_add : D ≤ Dθ + B * δ := by
        dsimp [D, Dθ]
        have hmul := mul_le_mul_of_nonneg_left hEZ_le_EZθ_add hB.le
        linarith
      have hDθpos : 0 < Dθ := by
        nlinarith
      have hTailCompare :
          3 * Real.exp
              (-((t / 2) / (K * B)) *
                Real.log
                  (1 + (B * (t / 2)) /
                    (sigmaSq + B * bernoulliExpectation p Zθ))) ≤
            3 * Real.exp
              (-(t / ((4 * K) * B)) *
                Real.log
                  (1 + (B * t) /
                    (sigmaSq + B * bernoulliExpectation p Z))) := by
        simpa [D, Dθ] using
          talagrand_log_tail_half_radius_le_four_constant
            hK hB htpos hDpos hDθpos hDθleD
      linarith
    · have hDzero : D = 0 := le_antisymm (le_of_not_gt hDpos) hD_nonneg
      have hprob_nonneg :
          0 ≤ bernoulliEventProb p
            (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t) :=
        bernoulli_event_prob_nonneg
          (fun Omega => |Z Omega - bernoulliExpectation p Z| ≤ t)
          hp_bounds.1 hp_bounds.2
      have hden :
          sigmaSq + B * bernoulliExpectation p Z = 0 := by
        simpa [D] using hDzero
      have hrhs :
          1 -
              3 * Real.exp
                (-(t / ((4 * K) * B)) *
                  Real.log
                    (1 + (B * t) /
                      (sigmaSq + B * bernoulliExpectation p Z))) = -2 := by
        rw [hden]
        norm_num
      linarith
  ·
    -- If the index class is empty, each supremum set is empty, hence `Z = 0`.
    have hZzero : Z = fun _ : Finset (Fin n₁ × Fin n₂) => (0 : ℝ) := by
      funext Omega
      have hempty :
          ({v : ℝ |
              ∃ a : ι,
                v =
                  ∑ i : Fin n₁, ∑ j : Fin n₂,
                    (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
                      coeff a i j)} : Set ℝ) = ∅ := by
        ext v
        constructor
        · intro hv
          rcases hv with ⟨a, ha⟩
          exact (hι ⟨a⟩).elim
        · intro hv
          simp at hv
      rw [hZ Omega, hempty]
      exact Real.sSup_empty
    subst Z
    have hmean : bernoulliExpectation p (fun _ : Finset (Fin n₁ × Fin n₂) => (0 : ℝ)) = 0 :=
      bernoulliExpectation_zero
    have htrue :
        (fun Omega : Finset (Fin n₁ × Fin n₂) =>
          |(fun _ : Finset (Fin n₁ × Fin n₂) => (0 : ℝ)) Omega -
              bernoulliExpectation p
                (fun _ : Finset (Fin n₁ × Fin n₂) => (0 : ℝ))| ≤ t)
          =
        (fun _ : Finset (Fin n₁ × Fin n₂) => True) := by
      funext Omega
      simp [hmean, ht]
    rw [htrue, bernoulliEventProb_true]
    exact one_sub_nonpos_tail_le_one (4 * K) B sigmaSq t
      (bernoulliExpectation p (fun _ : Finset (Fin n₁ × Fin n₂) => (0 : ℝ)))
      hB (by positivity)
