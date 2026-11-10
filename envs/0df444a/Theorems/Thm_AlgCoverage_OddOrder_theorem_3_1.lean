-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_theorem_3_1
-- name    : AlgCoverage.OddOrder.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:47:27.580377+00:00
-- url     : https://prove2.me/theorems/1f5ed659-2c57-47d8-b457-9accd41ec571
-- title:
--   Theorem 3.1 — uniform relative avoidance $\Pr(B\cap\mathcal W_k=\varnothing)=(1+o(1))e^{-\mu}$; error $\le e^{-\kappa k}\le N^{-\kappa}$ (iid), $2N^{-\kappa}$ (od) if $\ln N\ge2^{32}$
-- statement:
--   Let $G$ range over finite groups of odd order $N$, let $B\subseteq G\setminus\{1_G\}$ be deterministic with $m=|B|$, and let $k$ satisfy
--   $$1\le m\le N^{2^{-20}},\qquad \ln N\le k\le2\ln N,\qquad \nu:=m2^k/N\le2^{-79}\ln N. \tag{3.1}$$
--   With $\mu=m(2^k-1)/N$:
--
--   1. (3.2) Uniformly in the group and the target set, $\Pr_{\rm iid}(B\cap\mathcal W_k=\varnothing)=(1+o(1))e^{-\mu}$: for every $\varepsilon>0$ there is $N_0$ such that $|e^{\mu}\Pr_{\rm iid}(B\cap\mathcal W_k=\varnothing)-1|\le\varepsilon$ for all such data with $N\ge N_0$.
--   2. (3.2a) With $\kappa=2^{-27}$, for all admissible data with $\ln N\ge2^{32}$,
--   $$\big|e^{\mu}\Pr_{\rm iid}(B\cap\mathcal W_k=\varnothing)-1\big|\le e^{-\kappa k}\le N^{-\kappa}.$$
--   3. In the ordered-distinct model, for the same data, $\big|e^{\mu}\Pr_{\rm od}(B\cap\mathcal W_k=\varnothing)-1\big|\le2N^{-\kappa}$.
--
--   This relative estimate at logarithmic mean is the paper's main technical input to the coverage theorem.
--
--   Differences from the source:
--   - encoding: every finite group G of odd order → G : Type with [Group G] [Fintype G] and Odd (Fintype.card G); reason: every finite group is isomorphic to one in Type (universe 0), and every quantity in the statement is invariant under isomorphism
--   - encoding: uniformly in odd-order groups, (1 + o(1)) / → 0 / 'eventually' with one error function of N → ∀ ε > 0, ∃ N₀, ∀ G of odd order with |G| ≥ N₀ (and all admissible data); reason: a bound by one function of N tending to zero, independent of the group and data, is exactly this ε–N₀ statement
--   - encoding: probabilities and expectations over iid uniform inputs X ∈ G^k → counting ratios probIid / expIid (sums over G^k divided by N^k); reason: the iid law is uniform on the finite set G^k; same numbers
--   - encoding: uniform ordered k-tuple of distinct inputs (sampling without replacement), k ≤ N → probOd: #{injective x with A x}/#{injective x}; reason: uniform law on injective tuples; same numbers for legal k ≤ N
--   - reading: 'In the ordered-distinct model the same expression is at most 2N^{−κ}' → under the same admissible data with ln N ≥ 2^{32}; reason: Proposition A.1 states that ln N ≥ 2^{32} suffices for both the iid and the ordered-distinct bounds in (3.2a)
--   - encoding: N^{2^{−20}}, N^{−κ} → real powers Real.rpow; reason: N > 0, so the real power is the usual one
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 8 (PDF 9), Theorem 3.1, Eqs. (3.1), (3.2), (3.2a); proof §8.6 and §9.2, pp. 26–28 (PDF 27–29); App. A, p. 36 (PDF 37)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage
import Definitions.Def_AlgCoverage_OddOrder_Sieve

namespace AlgCoverage.OddOrder

/-- Theorem 3.1 (uniform relative avoidance), Lin, printed p. 8 / PDF 9. For a finite group `G` of odd
order `N`, a deterministic `B ⊆ G \ {1_G}` with `m = |B|`, and `k` with (3.1)
`1 ≤ m ≤ N^{2^{−20}}`, `ln N ≤ k ≤ 2 ln N`, `ν = m2^k/N ≤ 2^{−79} ln N`, and `µ = m(2^k − 1)/N`:
(3.2) `Pr(B ∩ 𝒲_k = ∅) = (1 + o(1)) e^{−µ}` with one error function of `N` for all groups and target
sets (iid inputs); (3.2a) with `κ = 2^{−27}`, for all admissible data with `ln N ≥ 2^{32}`:
`|e^µ Pr_iid(B ∩ 𝒲_k = ∅) − 1| ≤ e^{−κk} ≤ N^{−κ}`, and in the ordered-distinct model the same
expression is at most `2N^{−κ}`. -/
theorem theorem_3_1 :
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (G : Type) [Group G] [Fintype G],
      Odd (Fintype.card G) → N₀ ≤ Fintype.card G →
      ∀ (B : Finset G) (k : ℕ), (1 : G) ∉ B → 1 ≤ B.card →
        (B.card : ℝ) ≤ (Fintype.card G : ℝ) ^ ((2 : ℝ) ^ (-20 : ℤ)) →
        Real.log (Fintype.card G) ≤ k → (k : ℝ) ≤ 2 * Real.log (Fintype.card G) →
        paramNu B.card k (Fintype.card G) ≤ (2 : ℝ) ^ (-79 : ℤ) * Real.log (Fintype.card G) →
        |Real.exp (paramMu B.card k (Fintype.card G)) * probIid G k (Avoids B) - 1| ≤ ε) ∧
    (∀ (G : Type) [Group G] [Fintype G], Odd (Fintype.card G) →
      (2 : ℝ) ^ (32 : ℕ) ≤ Real.log (Fintype.card G) →
      ∀ (B : Finset G) (k : ℕ), (1 : G) ∉ B → 1 ≤ B.card →
        (B.card : ℝ) ≤ (Fintype.card G : ℝ) ^ ((2 : ℝ) ^ (-20 : ℤ)) →
        Real.log (Fintype.card G) ≤ k → (k : ℝ) ≤ 2 * Real.log (Fintype.card G) →
        paramNu B.card k (Fintype.card G) ≤ (2 : ℝ) ^ (-79 : ℤ) * Real.log (Fintype.card G) →
        |Real.exp (paramMu B.card k (Fintype.card G)) * probIid G k (Avoids B) - 1| ≤
            Real.exp (-((2 : ℝ) ^ (-27 : ℤ)) * k) ∧
          Real.exp (-((2 : ℝ) ^ (-27 : ℤ)) * k) ≤
            (Fintype.card G : ℝ) ^ (-((2 : ℝ) ^ (-27 : ℤ))) ∧
          |Real.exp (paramMu B.card k (Fintype.card G)) * probOd G k (Avoids B) - 1| ≤
            2 * (Fintype.card G : ℝ) ^ (-((2 : ℝ) ^ (-27 : ℤ)))) := by sorry

end AlgCoverage.OddOrder
