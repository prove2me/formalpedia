-- Prove2me | Theorems.Thm_Erdos287_gap_from_uniform_prime_window
-- name    : Erdos287.gap_from_uniform_prime_window
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:27:42.492589+00:00
-- url     : https://prove2.me/theorems/3e70d858-f359-4c15-a86f-7975e0b6a5ac
-- title:
--   A uniform prime-parameter window forces an Egyptian-fraction denominator gap
-- statement:
--   For $0<L\le U<\mathrm e L$ and an upper bound $A$ for slopes, there exist constants $0<\alpha<\beta$ and $M_0$ with the following property.
--
--   Suppose $1<n_0<\cdots<n_{k-1}=M$ have reciprocal sum one, with $M\ge M_0$. Let $S\subseteq\{0,\ldots,N-1\}$ be occupied labels with $(u+v)|S|>u(N+v)$, where $0<u$ and $2u\le v+2$. At some integer $t\in[\alpha M,\beta M]$, each occupied label $s$ has a prime $a(s)t+1$ with $1\le a(s)\le A$. Whenever $s,r\in S$ satisfy $u\le r-s\le v$, assume $d=a(r)-a(s)$ is positive and divides $a(s)$, and $L\le(a(s)/d)a(r)\le U$. Then some consecutive denominator gap is at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Builds on Erdos287.gap_from_dense_prime_form_groups.

import Mathlib

theorem Erdos287.gap_from_uniform_prime_window (A : ℕ) (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U)
    (hU : U < Real.exp 1 * L) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧ ∃ M₀ : ℕ,
    ∀ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k →
      (∀ i, i < k → 1 < f i) →
      (∀ i j, i < j → j < k → f i < f j) →
      (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) →
      M₀ ≤ f (k - 1) →
      ∀ (N u v t : ℕ) (S : Finset ℕ) (a : ℕ → ℕ),
        0 < u → 2 * u ≤ v + 2 →
        (∀ s ∈ S, s < N) →
        u * (N + v) < (u + v) * S.card →
        α * (f (k - 1) : ℝ) ≤ t → (t : ℝ) ≤ β * f (k - 1) →
        (∀ s ∈ S, 0 < a s ∧ a s ≤ A ∧ Nat.Prime (a s * t + 1)) →
        (∀ s ∈ S, ∀ r ∈ S, u ≤ r - s → r - s ≤ v →
        a s < a r ∧ (a r - a s) ∣ a s ∧
          L ≤ ((a s / (a r - a s) : ℕ) : ℝ) * a r ∧
          ((a s / (a r - a s) : ℕ) : ℝ) * a r ≤ U) →
        ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
