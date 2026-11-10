-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_corollary_3_2
-- name    : AlgCoverage.OddOrder.corollary_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:30.301143+00:00
-- url     : https://prove2.me/theorems/5c785fda-97c1-4a3f-9faf-3da7c5625ad5
-- title:
--   Corollary 3.2 — exact floor bounds for $\lambda_0$ and the one- and two-target seed $\Pr(B\cap\mathcal W_{k_0}=\varnothing)=(1+o(1))e^{-m\lambda_0}$
-- statement:
--   Put $c_N=\log_2(N\ln N)$, $k_0=\lfloor c_N-80\rfloor$ and $\lambda_0=(2^{k_0}-1)/N$. For every finite group of odd order $N>1$ the exact floor bounds hold:
--   $$2^{-81}\ln N-N^{-1}<\lambda_0\le2^{-80}\ln N-N^{-1}.$$
--   For $m=1,2$, uniformly over odd-order groups and over sets $B$ of $m$ distinct nonidentity targets, with iid inputs,
--   $$\Pr(B\cap\mathcal W_{k_0}=\varnothing)=(1+o(1))e^{-m\lambda_0}, \tag{3.3}$$
--   i.e. for every $\varepsilon>0$ there is $N_0$ with $|e^{m\lambda_0}\Pr_{\rm iid}(B\cap\mathcal W_{k_0}=\varnothing)-1|\le\varepsilon$ whenever $N\ge N_0$.
--
--   Differences from the source:
--   - encoding: every finite group G of odd order → G : Type with [Group G] [Fintype G] and Odd (Fintype.card G); reason: every finite group is isomorphic to one in Type (universe 0), and every quantity in the statement is invariant under isomorphism
--   - encoding: uniformly in odd-order groups, (1 + o(1)) / → 0 / 'eventually' with one error function of N → ∀ ε > 0, ∃ N₀, ∀ G of odd order with |G| ≥ N₀ (and all admissible data); reason: a bound by one function of N tending to zero, independent of the group and data, is exactly this ε–N₀ statement
--   - encoding: probabilities and expectations over iid uniform inputs X ∈ G^k → counting ratios probIid / expIid (sums over G^k divided by N^k); reason: the iid law is uniform on the finite set G^k; same numbers
--   - encoding: sample length k₀ = ⌊c_N − 80⌋ → Int.toNat (k0 N), with λ₀ = (2^{k₀} − 1)/N computed with the integer power; reason: k₀ ≥ 1 for all large N, where the two agree; only eventual (N ≥ N₀) statements use the length
--   - encoding: the floor bounds for the group order N → stated for odd N > 1; reason: c_N = log₂(N ln N) is undefined at N = 1 (ln 1 = 0)
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 8 (PDF 9), Corollary 3.2, Eq. (3.3)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage

namespace AlgCoverage.OddOrder

/-- Corollary 3.2 (one- and two-target seed), Lin, printed p. 8 / PDF 9. With `c_N = log₂(N ln N)`,
`k₀ = ⌊c_N − 80⌋`, `λ₀ = (2^{k₀} − 1)/N`: the exact floor bounds
`2^{−81} ln N − N^{−1} < λ₀ ≤ 2^{−80} ln N − N^{−1}` (for every odd order `N > 1`), and for `m = 1, 2`,
uniformly over odd-order groups and distinct nonidentity targets, `Pr(B ∩ 𝒲_{k₀} = ∅) = (1 + o(1))
e^{−mλ₀}` (3.3) (iid inputs). -/
theorem corollary_3_2 :
    (∀ (G : Type) [Group G] [Fintype G], Odd (Fintype.card G) → 1 < Fintype.card G →
      (2 : ℝ) ^ (-81 : ℤ) * Real.log (Fintype.card G) - 1 / (Fintype.card G : ℝ) <
          lam0 (Fintype.card G) ∧
        lam0 (Fintype.card G) ≤
          (2 : ℝ) ^ (-80 : ℤ) * Real.log (Fintype.card G) - 1 / (Fintype.card G : ℝ)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (G : Type) [Group G] [Fintype G],
      Odd (Fintype.card G) → N₀ ≤ Fintype.card G →
      ∀ B : Finset G, (1 : G) ∉ B → (B.card = 1 ∨ B.card = 2) →
        |Real.exp ((B.card : ℝ) * lam0 (Fintype.card G)) *
            probIid G (k0 (Fintype.card G)).toNat (Avoids B) - 1| ≤ ε) := by sorry

end AlgCoverage.OddOrder
