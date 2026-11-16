-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_theorem_2_2
-- name    : EliasGlobalClock.LowerBound.Supplement.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:35:49.884532+00:00
-- url     : https://prove2.me/theorems/17cd5ad3-1af8-4e3b-83cf-e524f9423475
-- title:
--   Theorem 2.2 — monotone codes from any summable profile, with |Code(N)| ≤ log₂ f(N) + log₂(2K)
-- statement:
--   Let $f:\mathbb Z_+\to\mathbb Z_+$ be nondecreasing with $\sum_{N\ge1}1/f(N)<K<\infty$ (the series converges and its sum is below $K$). Then there is a prefix-free code $\mathrm{Code}:\mathbb Z_+\to\{0,1\}^*$, with its sequence $(\mathrm{Int}(t))_{t\ge1}$, such that
--
--   1. **Code length.** For every $N\ge1$, $|\mathrm{Code}(N)|\le|\mathrm{Code}(N+1)|$ and
--   $$|\mathrm{Code}(N)|\le\log_2 f(N)+\log_2(2K);$$
--   2. **Monotonicity.** For every $N\ge1$, with $P=2^{|\mathrm{Code}(N)|}$, and every $j\ge0$, the sequence $(\mathrm{Int}(t))$ over positive $t\in[\,j(2P),(j+1)(2P)\,)$ contains $1,\dots,N$ as a subsequence.
--
--   The paper writes $|\mathrm{Code}(N)|\le\log_2f(N)+O(1)$; its proof (Appendix A.2) yields the constant $\log_2(2K)$, which is fixed before $N$ and depends only on $K$. This is the code used in the first clause of Theorem 3.1.
--
--   Differences from the source:
--   - generalization: |Code(N)| ≤ log₂ f(N) + O(1) → |Code(N)| ≤ log₂ f(N) + log₂(2K) for every N; reason: the explicit constant is the one Appendix A.2 derives (g(N) ≤ 2K f(N)); it implies the O(1) bound
--   - encoding: ∑_N 1/f(N) < K < ∞ → the real series of 1/f(N) over ℕ+ is Summable and its tsum is < K; reason: convergence is stated explicitly, so the tsum is never the default value of a divergent series
--   - encoding: Int(t) is the unique N whose codeword is a prefix of Bin_lsb(t)∥0^∞, or 0 → decode returns the unique positive N with that property, and 0 if none (or if not unique); reason: for a prefix-free code at most one codeword is a prefix of an infinite string, so the two agree
--   - encoding: (Int(t))_{t∈J} contains 1, 2, …, N as a subsequence → there are strictly increasing positive times τ_1<⋯<τ_N in J with Int(τ_i)=i; reason: definition of a subsequence; the sequence Int is indexed by positive times
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed pp.6–7 / PDF pp.7–8, Theorem 2.2; restated and proved printed p.23 / PDF p.24, Appendix A.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_codes

namespace EliasGlobalClock.LowerBound.Supplement

/-- Theorem 2.2 (printed pp.6–7 / PDF pp.7–8; restated and proved printed p.23 / PDF p.24).
For every nondecreasing `f : ℤ₊ → ℤ₊` with `∑_N 1/f(N) < K < ∞` there is a prefix-free code
with nondecreasing lengths, `|Code(N)| ≤ log₂ f(N) + log₂(2K)` (the `O(1)` of the source, with
the constant supplied by its proof), and the aligned `2P` monotonicity of its sequence
`Int`. The sum is a genuine convergent series. -/
theorem theorem_2_2 (f : ℕ+ → ℕ+) (hf : Monotone f) (K : ℝ)
    (hsum : Summable (fun N : ℕ+ => (1 : ℝ) / (f N : ℝ)))
    (hK : ∑' N : ℕ+, (1 : ℝ) / (f N : ℝ) < K) :
    ∃ c : ℕ+ → List Bool, IsPrefixFree c ∧
      (∀ N : ℕ+, (c N).length ≤ (c (N + 1)).length) ∧
      (∀ N : ℕ+, ((c N).length : ℝ) ≤ Real.logb 2 (f N : ℝ) + Real.logb 2 (2 * K)) ∧
      HasMonotonicity c := by sorry

end EliasGlobalClock.LowerBound.Supplement
