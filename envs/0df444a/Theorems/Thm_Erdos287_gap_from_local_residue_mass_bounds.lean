-- Prove2me | Theorems.Thm_Erdos287_gap_from_local_residue_mass_bounds
-- name    : Erdos287.gap_from_local_residue_mass_bounds
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:54:11.307801+00:00
-- url     : https://prove2.me/theorems/521b3026-bacd-4fca-8172-9cf26d80f7ce
-- title:
--   Local prime-power omission bounds combine across overlapping denominator sets
-- statement:
--   Consider a strictly increasing list of positive integers greater than one with reciprocal sum one. Let $m$ and $M$ be its first and last terms. Take a finite family of candidate sets $S_j$ in $[m,M]$, each with its own list of prime-power congruences covering the relevant valuation layers, rational omission charges $c_j(n)$, and a local lower bound $B_j$. For each $j$, assume that every subset $T\subseteq S_j$ respecting the specified congruences, omitting the prescribed holes, including any endpoint in $S_j$, and never omitting adjacent candidates of $S_j$, has omitted charge $\sum_{n\in S_j\setminus T}c_j(n)\ge B_j$.
--
--   If $\sum_{j:n\in S_j}c_j(n)\le 1/n$ for each $n\in[m,M]$, and $\sum_j B_j>\sum_{n=m}^M 1/n-1$, then some consecutive gap in the list is at least three. The sets $S_j$ may overlap.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Local aggregation of the certified omission mass in https://prove2.me/theorems/06048221-89bb-49b6-bd3d-d84d24d99631.

import Mathlib

theorem Erdos287.gap_from_local_residue_mass_bounds (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (r : ℕ) (s : Fin r → ℕ) (S : Fin r → Finset ℕ)
    (p b a L : (j : Fin r) → Fin (s j) → ℕ)
    (hp : ∀ j u, (p j u).Prime) (hb : ∀ j u, 1 ≤ b j u)
    (hba : ∀ j u, b j u ≤ a j u)
    (hspan : ∀ j n, n ∈ S j → f 0 ≤ n ∧ n ≤ f (k - 1))
    (hcover : ∀ j u i, i < k → b j u ≤ padicValNat (p j u) (f i) → f i ∈ S j)
    (hcoeff : ∀ j u i, i < k → b j u ≤ padicValNat (p j u) (f i) →
      padicValNat (p j u) (f i) ≤ a j u ∧
        f i / p j u ^ padicValNat (p j u) (f i) ∣ L j u)
    (H : Finset ℕ) (hH : ∀ i, i < k → f i ∉ H)
    (c : Fin r → ℕ → ℚ) (B : Fin r → ℚ)
    (hcharge : ∀ n, f 0 ≤ n → n ≤ f (k - 1) →
      (∑ j : Fin r, if n ∈ S j then c j n else 0) ≤ (1 : ℚ) / n)
    (hlocal : ∀ j (T : Finset ℕ), T ⊆ S j → Disjoint T H →
      (f 0 ∈ S j → f 0 ∈ T) → (f (k - 1) ∈ S j → f (k - 1) ∈ T) →
      (∀ n ∈ S j, n + 1 ∈ S j → n ∉ T → n + 1 ∈ T) →
      (∀ u, p j u ^ (a j u + 1 - b j u) ∣
        ∑ n ∈ T, if b j u ≤ padicValNat (p j u) n then
          (L j u / (n / p j u ^ padicValNat (p j u) n)) *
            p j u ^ (a j u - padicValNat (p j u) n) else 0) →
      B j ≤ ∑ n ∈ S j \ T, c j n)
    (hbudget : (∑ n ∈ Finset.Icc (f 0) (f (k - 1)), (1 : ℚ) / n) - 1 < ∑ j, B j) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
