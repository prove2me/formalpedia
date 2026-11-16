-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_B_1
-- name    : ElimAgree.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:41:31.433204+00:00
-- url     : https://prove2.me/theorems/c7184b24-c838-4d51-8797-26f2ea97b9f6
-- title:
--   Theorem B.1 (Deterministic one-way restricted inner product)
-- statement:
--   For $1\le k\le n$,
--
--   $$M^*(n,k)\ \ge\ \max\Big\{2,\ \frac{2^{n-k}}{k\ln2}\Big\},$$
--
--   and for $8\le k\le n$,
--
--   $$M^*(n,k)\ \le\ (1+\varepsilon_k)\frac{2^{n-k}}{k\ln2}+2.$$
--
--   Consequently, for $8\le k\le n$,
--
--   $$n-k-\log(k\ln2)\le\log M^*(n,k)\le n-k-\log(k\ln2)+\log(1+\varepsilon_k)+2k2^{k-n},\tag{B.1}$$
--
--   and in all cases ($n,k\ge1$) $D^{B\to A,A}(\mathrm{REIP}_{n,k})=\max\{n-k-\log k,0\}+O(1)$, with an absolute constant. For $k>n$ no communication is needed: $M^*(n,k)=1$.
--
--   This determines the deterministic one-way complexity of restricted inner product up to an additive $o(1)$ inside a ceiling.
--
--   **Formalization Note** $D^{B\to A,A}=\lceil\log M^*\rceil$ as on p.30.
--
--   Differences from the source:
--   - reading: "in all cases" D^{B→A,A}(REIP_{n,k}) = max{n − k − log k, 0} + O(1) → ∃ absolute C with |D − max{…}| ≤ C for all n, k ≥ 1; reason: O(1) is an absolute constant
--   - reading: for k > n no communication is needed → M*(n, k) = 1 for all n < k; reason: a single message is no communication
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem B.1, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_ElimAgree_Supplement_REIP

namespace ElimAgree

namespace Supplement

/-- Theorem B.1 (Deterministic one-way restricted inner product), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.30. For `1 ≤ k ≤ n`,
`M*(n, k) ≥ max{2, 2^{n−k}/(k ln 2)}`, and for `8 ≤ k ≤ n`, `M*(n, k) ≤ (1 + ε_k) 2^{n−k}/(k ln 2) + 2`.
Consequently, for `8 ≤ k ≤ n`,
`n − k − log(k ln 2) ≤ log M*(n, k) ≤ n − k − log(k ln 2) + log(1 + ε_k) + 2k2^{k−n}` (B.1), and in all
cases `D^{B→A,A}(REIP_{n,k}) = max{n − k − log k, 0} + O(1)`. For `k > n` no communication is needed.

**Formalization Note.** `log` is `Real.logb 2`. "In all cases" is all `n, k ≥ 1`, with `O(1)` an
absolute constant `C` chosen before `n` and `k`. "No communication is needed" is `M*(n, k) = 1`: one
message suffices. -/
theorem theorem_B_1 :
    (∀ n k : ℕ, 1 ≤ k → k ≤ n →
      max 2 ((2 : ℝ) ^ (n - k) / (k * Real.log 2)) ≤ (Mstar n k : ℝ)) ∧
    (∀ n k : ℕ, 8 ≤ k → k ≤ n →
      (Mstar n k : ℝ) ≤ (1 + epsK k) * (2 : ℝ) ^ (n - k) / (k * Real.log 2) + 2) ∧
    (∀ n k : ℕ, 8 ≤ k → k ≤ n →
      (n : ℝ) - k - Real.logb 2 (k * Real.log 2) ≤ Real.logb 2 (Mstar n k) ∧
      Real.logb 2 (Mstar n k) ≤ (n : ℝ) - k - Real.logb 2 (k * Real.log 2) +
        Real.logb 2 (1 + epsK k) + 2 * k * (2 : ℝ) ^ ((k : ℤ) - n)) ∧
    (∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      |(DBA n k : ℝ) - max ((n : ℝ) - k - Real.logb 2 k) 0| ≤ C) ∧
    (∀ n k : ℕ, n < k → Mstar n k = 1) := by sorry

end Supplement

end ElimAgree
