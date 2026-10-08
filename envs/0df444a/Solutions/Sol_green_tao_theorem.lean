-- Prove2me | solution 1 for green_tao_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T09:47:44.713058+00:00
-- url     : https://prove2.me/submissions/ee174488-e446-4144-bcd6-a61653e394fe
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

/-- The primes have non-summable reciprocals (Mathlib). -/
theorem not_summable_primes : ¬ Summable fun p : {p : ℕ | p.Prime} ↦ 1 / (p : ℝ) :=
  Nat.Primes.not_summable_one_div

theorem primes_hasAP (k : ℕ) : ∃ a d : ℕ, 0 < d ∧ ∀ i < k, (a + i * d).Prime :=
  hasAP_of_not_summable not_summable_primes k

end OAIErdos3Cor

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    ∃ a d : ℕ, 1 ≤ d ∧ ∀ j : Fin k, Nat.Prime (a + j.val * d) := by
  obtain ⟨a, d, hd, h⟩ := OAIErdos3Cor.primes_hasAP k
  exact ⟨a, d, hd, fun j ↦ h j.val j.isLt⟩
