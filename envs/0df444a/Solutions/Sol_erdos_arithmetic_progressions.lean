-- Prove2me | solution 1 for erdos_arithmetic_progressions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T09:47:46.58218+00:00
-- url     : https://prove2.me/submissions/0eb8764e-721b-4be7-a3b5-3a069a43c369
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos142Basic
import Theorems.Thm_Erdos3_erdos_3

namespace OAIErdos3Cor

open Erdos142

/-- From the published Erdős Problem 3 statement: a set with non-summable reciprocals contains a
`k`-term progression with positive common difference, for every `k`. -/
theorem hasAP_of_not_summable {A : Set ℕ} (hA : ¬ Summable fun a : A ↦ 1 / (a : ℝ)) (k : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  obtain ⟨m, ⟨S, hSA, a, d, hcard, hS⟩, hm⟩ :=
    ((Erdos3.erdos_3 A hA).and_eventually (Filter.eventually_ge_atTop (k + 2))).exists
  have hcard' : S.encard = (m : ℕ∞) := hcard
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      subst h0
      have hsub : S ⊆ {a} := by
        rw [hS]
        rintro _ ⟨n, _, rfl⟩
        simp
      have h1 : S.encard ≤ 1 := (Set.encard_le_encard hsub).trans_eq (Set.encard_singleton a)
      rw [hcard'] at h1
      have : m ≤ 1 := by exact_mod_cast h1
      omega
    · exact h0
  refine ⟨a, d, hd, fun i hi ↦ hSA ?_⟩
  rw [hS]
  exact ⟨i, by exact_mod_cast (show i < m by omega), by simp⟩

/-- Partial sums that are unbounded force non-summability. -/
theorem not_summable_of_unbounded (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA_div : ∀ M : ℝ, ∃ N : ℕ, M ≤
      ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / (n : ℝ)) :
    ¬ Summable fun a : A ↦ 1 / (a : ℝ) := by
  intro hs
  have hs' : Summable (A.indicator fun n : ℕ ↦ 1 / (n : ℝ)) :=
    summable_subtype_iff_indicator.mp hs
  obtain ⟨N, hN⟩ := hA_div (∑' n, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n + 1)
  have hle : ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / (n : ℝ) ≤
      ∑' n, A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n := by
    rw [Finset.sum_filter]
    have heq : ∀ n ∈ Finset.Icc 1 N, (if n ∈ A then (1 : ℝ) / (n : ℝ) else 0) =
        A.indicator (fun n : ℕ ↦ 1 / (n : ℝ)) n := by
      intro n _
      simp only [Set.indicator_apply]
    rw [Finset.sum_congr rfl heq]
    exact hs'.sum_le_tsum _ fun n _ ↦ Set.indicator_nonneg (fun n _ ↦ by positivity) n
  linarith

end OAIErdos3Cor

theorem solution (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA_pos : ∀ n ∈ A, 0 < n)
    (hA_div : ∀ M : ℝ, ∃ N : ℕ, M ≤
      ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / (n : ℝ)) :
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i < k, (a + i * d) ∈ A :=
  OAIErdos3Cor.hasAP_of_not_summable (OAIErdos3Cor.not_summable_of_unbounded A hA_div)
