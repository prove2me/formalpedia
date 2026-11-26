-- Prove2me | Theorems.Thm_Erdos287_gap_from_dense_prime_form_groups
-- name    : Erdos287.gap_from_dense_prime_form_groups
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:20:20.569957+00:00
-- url     : https://prove2.me/theorems/010cd676-ddce-50fa-a6c5-4f30a71ca362
-- title:
--   Dense occupied groups of prime affine forms force a denominator gap
-- statement:
--   Let $1<n_0<\cdots<n_{k-1}=M$ have reciprocal sum one. Consider occupied group labels $S\subseteq\{0,\ldots,N-1\}$, each carrying a prime $a(s)t+1$ at a common parameter $t$. Fix positive $u$ and $v\ge2u-2$. Suppose $(u+v)|S|>u(N+v)$ and every occupied prime satisfies the logarithmic cofactor exclusion for the bound $M$.
--
--   Assume that whenever occupied labels $s<r$ satisfy $u\le r-s\le v$, the difference $d=a(r)-a(s)$ is positive and divides $a(s)$, and $x=(a(s)/d)(a(r)t+1)$ satisfies $x+1\le M<\mathrm e x$. Then at least one consecutive denominator gap is at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. The affine pair construction is related to Ford–Maynard, Theorem 7.19 in https://ford126.web.illinois.edu/sieve2023.pdf. The relevant group-occupancy method is Merikoski, Proposition 19 in https://arxiv.org/abs/1811.03008.

import Mathlib

theorem Erdos287.gap_from_dense_prime_form_groups (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (N u v t : ℕ) (S : Finset ℕ) (a : ℕ → ℕ) (hu : 0 < u) (hv : 2 * u ≤ v + 2)
    (hS : ∀ s ∈ S, s < N) (hdensity : u * (N + v) < (u + v) * S.card)
    (hprime : ∀ s ∈ S, Nat.Prime (a s * t + 1))
    (hlarge : ∀ s ∈ S, let p := a s * t + 1; let B := f (k - 1) / p
      Real.log B + Chebyshev.psi B < Real.log p)
    (hpairs : ∀ s ∈ S, ∀ r ∈ S, u ≤ r - s → r - s ≤ v →
      let d := a r - a s
      let x := (a s / d) * (a r * t + 1)
      a s < a r ∧ d ∣ a s ∧ x + 1 ≤ f (k - 1) ∧ (f (k - 1) : ℝ) < Real.exp 1 * x) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
