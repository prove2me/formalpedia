-- Prove2me | Theorems.Thm_CyclicForrelation_Even_Supplement_adaptive_lower_bound
-- name    : CyclicForrelation.Even.Supplement.adaptive_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:49:38.483657+00:00
-- url     : https://prove2.me/theorems/945e4464-035f-417f-9bc5-8020a534ef97
-- title:
--   Theorem 16 — adaptive classical lower bound $\Omega(N^{1/4})$ for every $k\ge4$
-- statement:
--   Let $n\in\mathbb N$, $N=2^n$, $k\ge4$ an integer (even or odd) and $0<\varepsilon<1/2$. Let $T_k(f_1,\dots,f_k)=\frac1N\operatorname{Tr}(D_{f_1}H^{\otimes n}\cdots D_{f_k}H^{\otimes n})$ be the $k$-cyclic Forrelation of sign functions $f_j:\mathbb F_2^n\to\{-1,1\}$, and let $R^{\mathrm{ad}}_\varepsilon(T_k)$ be the least worst-case total number of queries of a randomized adaptive classical algorithm that estimates $T_k$ to additive error $\varepsilon$ with probability at least $2/3$ on every input. Then
--   $$R^{\mathrm{ad}}_\varepsilon(T_k)\ge\tfrac12\,N^{1/4}.$$
--   Adaptive algorithms may choose each query based on all previous answers, stop early, repeat queries and use arbitrary private randomness; their cost is the total number of queries to all $k$ functions on the worst input and seed.
--
--   This is the only lower bound in the paper against adaptive algorithms; it holds uniformly in $k$ and $\varepsilon$.
--
--   **Formalization Note** The printed $\Omega$ is instantiated by the absolute certificate $1/2$, read off the paper's proof (pp. 21–22). For $n\ge1$, $\max\{|L|,|L^\perp|\}=2^{\lceil n/2\rceil}\le2\sqrt N$, so the collision probability is at most $\binom q2\cdot2/\sqrt N\le q^2/\sqrt N$; success $2/3\le\frac12+\Pr[C]/2$ forces $q^2\ge\sqrt N/3$, i.e. $q\ge N^{1/4}/\sqrt3\ge N^{1/4}/2$. At $n=0$ the target is the product of $k$ oracle signs, which forces $q\ge k\ge4>1/2$. The power $N^{1/4}$ is a real power.
--
--   Differences from the source:
--   - generalization: Ω(N^{1/4}) with an unspecified absolute constant → the numerical lower certificate N^{1/4}/2, independent of n, k and ε; reason: the collision bound on pp. 21–22 gives this certificate for all n ≥ 1, the n = 0 case is direct, and it implies the printed Ω bound
--   - encoding: minimum total worst-case adaptive queries at success 2/3 (footnote 2, p. 4) → least achievable natural cost adaptiveComplexity in the measurable private-seed adaptive model, where the next query and the output depend only on the seed and the answers so far; reason: this is a general randomized decision tree with early stopping and repeated queries, and exhaustive feasibility is proved before minimization
--   - encoding: one-based sign functions f_1,…,f_k on F_2^n → zero-based Fin k indices and Boolean signs read as real ±1; reason: bijective encoding preserving every input tuple and the closing cycle edge
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 21, Theorem 16, Eq. (33); proof pp. 21–22; adaptive model p. 4, §1.1 and footnote 2

import Definitions.Def_CyclicForrelation_Even_Supplement_adaptiveComplexity
import Definitions.Def_CyclicForrelation_Even_Supplement_hiddenSubspace

namespace CyclicForrelation.Even.Supplement

/-- Theorem 16 (every k ≥ 4), with the uniform certificate 1/2 for the paper's Ω. -/
theorem adaptive_lower_bound (n k : ℕ) (hk : 4 ≤ k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    (1 / 2 : ℝ) * (cubeSize n : ℝ) ^ ((1 : ℝ) / 4) ≤ (adaptiveComplexity n k ε : ℝ) := by sorry

end CyclicForrelation.Even.Supplement
