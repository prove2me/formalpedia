-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_theorem_3_4
-- name    : AlgCoverage.OddOrder.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:47:36.944657+00:00
-- url     : https://prove2.me/theorems/503aba92-15c8-46dc-9b0f-95106d518437
-- title:
--   Theorem 3.4 — uniform coverage and medians of odd-order groups: $\Pr(\mathcal W_{k_0}=G)\to0$, coverage once $2^k/N-\ln N\to\infty$, $c_N-80<f_\star(G)\le\lceil c_N+1\rceil$, both sampling models
-- statement:
--   Let $G$ range over finite groups of odd order $N$; let $c_N=\log_2(N\ln N)$, $k_0=\lfloor c_N-80\rfloor$ and $\lambda_0=(2^{k_0}-1)/N$. Inputs are either iid uniform (any length $k$) or a uniform ordered sample without replacement (legal lengths $k\le N$). Uniformly in odd-order groups:
--
--   1. **Non-coverage at the seed.** $\Pr(\mathcal W_{k_0}=G)\to0$ in both models: for every $\varepsilon>0$ there is $N_0$ with $\Pr_{\rm iid}(\mathcal W_{k_0}=G)\le\varepsilon$ and $\Pr_{\rm od}(\mathcal W_{k_0}=G)\le\varepsilon$ for every odd-order $G$ with $N\ge N_0$.
--   2. **Coverage above the window.** For any legal length with $2^k/N-\ln N\to+\infty$, coverage has probability tending to one: for every $\varepsilon>0$ there are $T$ and $N_0$ such that every $G$ with $N\ge N_0$ and every $k$ with $2^k/N-\ln N\ge T$ has $\Pr_{\rm iid}(\mathcal W_k=G)\ge1-\varepsilon$, and also $\Pr_{\rm od}(\mathcal W_k=G)\ge1-\varepsilon$ when $k\le N$.
--   3. **Median window.** The integer medians $f_{\rm iid}(G)$, $f_{\rm od}(G)$ (least legal length with coverage probability at least $1/2$) satisfy, eventually,
--   $$c_N-80<f_\star(G)\le\lceil c_N+1\rceil,\qquad\star\in\{\rm iid,od\}. \tag{3.4}$$
--   4. **Seed transfer.** The seed avoidance estimates hold for sampling without replacement: for $m=1,2$ distinct nonidentity targets, $e^{m\lambda_0}\Pr_{\rm od}(B\cap\mathcal W_{k_0}=\varnothing)\to1$ (Corollary 3.2's (3.3)); and for $1\le m\le N^{2^{-20}}$ nonidentity targets at the adjusted seed $k_B=\lfloor\log_2(N\ln N/m)-80\rfloor$, $e^{\mu}\Pr_{\rm od}(B\cap\mathcal W_{k_B}=\varnothing)\to1$ with $\mu=m(2^{k_B}-1)/N$ (Corollary 3.3), uniformly in the target sets.
--
--   In particular $f_\star(G)=\log_2N+\log_2\ln N+O(1)$ with an absolute constant, for every group of odd order, abelian or not.
--
--   Differences from the source:
--   - encoding: every finite group G of odd order → G : Type with [Group G] [Fintype G] and Odd (Fintype.card G); reason: every finite group is isomorphic to one in Type (universe 0), and every quantity in the statement is invariant under isomorphism
--   - encoding: uniformly in odd-order groups, (1 + o(1)) / → 0 / 'eventually' with one error function of N → ∀ ε > 0, ∃ N₀, ∀ G of odd order with |G| ≥ N₀ (and all admissible data); reason: a bound by one function of N tending to zero, independent of the group and data, is exactly this ε–N₀ statement
--   - encoding: probabilities and expectations over iid uniform inputs X ∈ G^k → counting ratios probIid / expIid (sums over G^k divided by N^k); reason: the iid law is uniform on the finite set G^k; same numbers
--   - encoding: uniform ordered k-tuple of distinct inputs (sampling without replacement), k ≤ N → probOd: #{injective x with A x}/#{injective x}; reason: uniform law on injective tuples; same numbers for legal k ≤ N
--   - encoding: sample length k₀ = ⌊c_N − 80⌋ → Int.toNat (k0 N), with λ₀ = (2^{k₀} − 1)/N computed with the integer power; reason: k₀ ≥ 1 for all large N, where the two agree; only eventual (N ≥ N₀) statements use the length
--   - encoding: 'for any legal input length with 2^k/N − ln N → +∞, coverage has probability tending to one' → ∀ ε > 0, ∃ T N₀, ∀ G odd with N ≥ N₀, ∀ k with 2^k/N − ln N ≥ T: coverage probability ≥ 1 − ε (od: also k ≤ N); reason: equivalent to the sequential form along every sequence of groups and legal lengths with diverging gap
--   - encoding: f_⋆(G) = least legal length with coverage probability ≥ 1/2 → fIid G = sInf {k | 1/2 ≤ covIid G k}, fOd G = sInf {k | k ≤ N ∧ 1/2 ≤ covOd G k}; reason: both sets are nonempty (od: k = N covers surely; iid: coverage probability → 1), so sInf is the minimum
--   - encoding: c_N − 80 < f_⋆(G) ≤ ⌈c_N + 1⌉ → a real strict inequality and an integer inequality against Int.ceil; reason: c_N is real and ⌈c_N + 1⌉ an integer
--   - reading: 'The seed avoidance estimates also transfer to sampling without replacement' → the ordered-distinct versions of both seed estimates: Corollary 3.2's (3.3) for m = 1, 2 at k₀ and Corollary 3.3's adjusted seed k_B for 1 ≤ m ≤ N^{2^{−20}}; reason: 'seed avoidance estimates' is plural and §9.2 states the transfer 'including the adjusted growing-target seed'; the stronger reading
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 8 (PDF 9), Theorem 3.4, Eq. (3.4); proof §9, pp. 27–28 (PDF 28–29)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage
import Definitions.Def_AlgCoverage_OddOrder_Sieve

namespace AlgCoverage.OddOrder

/-- Theorem 3.4 (coverage and medians), Lin, printed p. 8 / PDF 9. For finite groups `G` of odd order
`N`, with `c_N = log₂(N ln N)`, `k₀ = ⌊c_N − 80⌋` and `λ₀ = (2^{k₀} − 1)/N`, in both the iid model and
the ordered-distinct model (uniform injective `k`-tuples, legal for `k ≤ N`), uniformly in `G`:
(i) `Pr(𝒲_{k₀} = G) → 0`;
(ii) coverage has probability tending to one for any legal `k` with `2^k/N − ln N → +∞`;
(iii) eventually `c_N − 80 < f_⋆(G) ≤ ⌈c_N + 1⌉` for both medians `f_iid`, `f_od`;
(iv) the seed avoidance estimates transfer to sampling without replacement: Corollary 3.2's (3.3)
(`m = 1, 2` at `k₀`) and Corollary 3.3's adjusted seed (`1 ≤ m ≤ N^{2^{−20}}` at `k_B`). -/
theorem theorem_3_4 :
    -- (i) non-coverage at the seed length `k₀`, both models
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (G : Type) [Group G] [Fintype G],
      Odd (Fintype.card G) → N₀ ≤ Fintype.card G →
        covIid G (k0 (Fintype.card G)).toNat ≤ ε ∧ covOd G (k0 (Fintype.card G)).toNat ≤ ε) ∧
    -- (ii) coverage once `2^k/N − ln N → +∞`, both models (od: legal `k ≤ N`)
    (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∃ N₀ : ℕ, ∀ (G : Type) [Group G] [Fintype G],
      Odd (Fintype.card G) → N₀ ≤ Fintype.card G →
      ∀ k : ℕ, T ≤ (2 : ℝ) ^ k / (Fintype.card G : ℝ) - Real.log (Fintype.card G) →
        1 - ε ≤ covIid G k ∧ (k ≤ Fintype.card G → 1 - ε ≤ covOd G k)) ∧
    -- (iii) the median window (3.4), both models
    (∃ N₀ : ℕ, ∀ (G : Type) [Group G] [Fintype G],
      Odd (Fintype.card G) → N₀ ≤ Fintype.card G →
        cN (Fintype.card G) - 80 < (fIid G : ℝ) ∧ (fIid G : ℤ) ≤ ⌈cN (Fintype.card G) + 1⌉ ∧
        cN (Fintype.card G) - 80 < (fOd G : ℝ) ∧ (fOd G : ℤ) ≤ ⌈cN (Fintype.card G) + 1⌉) ∧
    -- (iv) the seed avoidance estimates in the ordered-distinct model
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (G : Type) [Group G] [Fintype G],
      Odd (Fintype.card G) → N₀ ≤ Fintype.card G →
        (∀ B : Finset G, (1 : G) ∉ B → (B.card = 1 ∨ B.card = 2) →
          |Real.exp ((B.card : ℝ) * lam0 (Fintype.card G)) *
              probOd G (k0 (Fintype.card G)).toNat (Avoids B) - 1| ≤ ε) ∧
        (∀ B : Finset G, (1 : G) ∉ B → 1 ≤ B.card →
          (B.card : ℝ) ≤ (Fintype.card G : ℝ) ^ ((2 : ℝ) ^ (-20 : ℤ)) →
          |Real.exp (paramMu B.card (kB (Fintype.card G) B.card).toNat (Fintype.card G)) *
              probOd G (kB (Fintype.card G) B.card).toNat (Avoids B) - 1| ≤ ε)) := by sorry

end AlgCoverage.OddOrder
