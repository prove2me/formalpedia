-- Prove2me | Theorems.Thm_CliffordHierTest_theorem_19
-- name    : CliffordHierTest.theorem_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:06.81962+00:00
-- url     : https://prove2.me/theorems/9e8eec10-5699-4ea3-be1a-8aa884163073
-- title:
--   Theorem 19 — 99% inverse theorem for $1\le k\le4$, with $\varepsilon_k=24^{-k}$, $C_k=24^{k-1}$
-- statement:
--   Let $1\le k\le4$, let $d$ be prime, and set $\varepsilon_1=1$, $C_1=1$ and $\varepsilon_k=1/24^k$, $C_k=24^{k-1}$ for $2\le k\le4$. For all $n\ge1$, all $0<\varepsilon\le\varepsilon_k$ and all $U\in\mathcal U(d^n)$,
--   $$\|U\|_{P^k}^{2^k}\ge1-\varepsilon\ \Longrightarrow\ \mathcal F_{\mathcal C^{(k-1)}}(U)\ge1-C_k\varepsilon.$$
--
--   The printed statement asserts the existence of constants $0<\varepsilon_k\le1$ and $C_k\ge1$; the values above are those fixed in its proof (p.8 for $k=1$, p.11 for $2\le k\le4$). The case $k=4$ gives Theorem 2.
--
--   Differences from the source:
--
--   - generalization: for all 1 ≤ k ≤ 4 and prime d there exist constants 0 < ε_k ≤ 1, C_k ≥ 1 → the explicit constants ε₁ = C₁ = 1, ε_k = 1/24^k, C_k = 24^{k−1} (2 ≤ k ≤ 4), independent of d; reason: these are the values fixed in the proof (pp.8, 11); they satisfy 0 < ε_k ≤ 1 and C_k ≥ 1, so the statement implies the printed one
--   - encoding: ℱ_𝒮(U) = max_{V∈𝒮} |⟨V,U⟩|² → sSup of the values |⟨V,U⟩|², V ∈ 𝒮; reason: the set is nonempty and bounded and the maximum is attained, so the supremum is the maximum
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §4 Theorem 19, p.8; constants ε₁ = C₁ = 1, p.8, and ε_k = 1/24^k, C_k = 24^{k−1}, p.11

import Mathlib
import Definitions.Def_CliffordHierTest_Hierarchy

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Theorem 19** (pp.8, 11), with the constants fixed in its proof. Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
For `1 ≤ k ≤ 4`, prime `d`, `n ≥ 1`, `0 < ε ≤ ε_k` and `U ∈ 𝒰(dⁿ)`: if
`‖U‖_{P^k}^{2^k} ≥ 1 − ε` then `ℱ_{𝒞^{(k-1)}}(U) ≥ 1 − C_k ε`, with `ε₁ = 1`, `C₁ = 1` (p.8) and
`ε_k = 1/24^k`, `C_k = 24^{k-1}` for `2 ≤ k ≤ 4` (p.11).

**Formalization Note.** The printed statement says "there exist constants `0 < ε_k ≤ 1` and
`C_k ≥ 1`" after "for all `1 ≤ k ≤ 4` and prime number `d`"; the proof fixes the explicit
values above, which do not depend on `d`. They are written in (`C₁ = 24⁰ = 1`), so the statement
implies the printed one. -/
theorem theorem_19 (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (d : ℕ) [Fact (Nat.Prime d)] (n : ℕ)
    (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) (hεk : ε ≤ (if k = 1 then (1 : ℝ) else 1 / (24 : ℝ) ^ k))
    (U : QuditUnitary d n) (hU : 1 - ε ≤ pauliNorm k (U : QuditOperator d n) ^ (2 ^ k)) :
    1 - (24 : ℝ) ^ (k - 1) * ε ≤ cliffordFid (k - 1) (U : QuditOperator d n) := by sorry

end CliffordHierTest
