-- Prove2me | Theorems.Thm_CyclicForrelation_Even_Supplement_odd_nonadaptive_lower_bound
-- name    : CyclicForrelation.Even.Supplement.odd_nonadaptive_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:48:41.2172+00:00
-- url     : https://prove2.me/theorems/22074ca5-6e04-4677-a978-f5f4af72cd98
-- title:
--   Theorem 8 — odd-cycle nonadaptive lower bound
-- statement:
--   Let $n\in\mathbb N$, $N=2^n$, $m\ge2$ and $0<\varepsilon<1/2$. Let $T_{2m+1}(f_1,\dots,f_{2m+1})=\frac1N\operatorname{Tr}(D_{f_1}H^{\otimes n}\cdots D_{f_{2m+1}}H^{\otimes n})$ be the $(2m+1)$-cyclic Forrelation of sign functions $f_j:\mathbb F_2^n\to\{-1,1\}$, and let $R^{\mathrm{na}}_\varepsilon(T_{2m+1})$ be the least worst-case total number of queries of a randomized nonadaptive classical algorithm that estimates $T_{2m+1}$ to additive error $\varepsilon$ with probability at least $2/3$ on every input. Then
--   $$R^{\mathrm{na}}_\varepsilon(T_{2m+1})\ge\frac{m}{96}\min\bigl\{N,\;N^{1-1/m}\varepsilon^{-2/m}\bigr\}.$$
--   The bound holds for every $n$, with an absolute constant, and includes both the accuracy-dependent regime and saturation at scale $mN$.
--
--   Together with the even-cycle bounds of this mission, this gives the odd-cycle lower bound $\Omega_k(N^{1-2/(k-1)})$ for constant accuracy and odd $k\ge5$.
--
--   **Formalization Note** The printed $\Omega$ is instantiated by the absolute certificate $1/96$, read off the paper's proof (pp. 15–16). Eq. (24) gives $q\ge m3^{-1/m}N^{1-1/m}$. For $\sqrt{3/N}\le\varepsilon\le1/16$ the bias-$8\varepsilon$ testing argument (with $|c_n|\ge1/2$, $|w_y|\le1$) gives $q\ge(m/48)N^{1-1/m}\varepsilon^{-2/m}$. If $N\ge768$ and $\varepsilon<\sqrt{3/N}$, monotonicity at $\sqrt{3/N}$ gives $q\ge mN/96$. If $\varepsilon>1/16$, Eq. (24) dominates since $(3\cdot16^2)^{1/m}<96$. If $N<768$, $(3N)^{1/m}<48$ makes Eq. (24) at least $mN/48$. The scale $\min\{N,N^{1-1/m}\varepsilon^{-2/m}\}$ is the published `evenScale n m ε`; the name refers to its first use, and it carries no parity hypothesis.
--
--   Differences from the source:
--   - generalization: Ω(m min{N, N^{1−1/m} ε^{−2/m}}) with an unspecified absolute constant → the numerical lower certificate m/96, independent of n, m and ε; reason: Eq. (24) and the testing argument on pp. 15–16 give this certificate throughout the stated domain, and it implies the printed Ω bound
--   - encoding: minimum total worst-case nonadaptive queries at success 2/3 → the published least achievable natural cost nonadaptiveComplexity in the measurable private-seed query-list model; reason: queries are fixed before answers, postprocessing sees only the seed and answers, and exhaustive feasibility is proved before minimization
--   - encoding: one-based sign functions f_1,…,f_{2m+1} on F_2^n → zero-based Fin (2m+1) indices and Boolean signs read as real ±1; reason: bijective encoding preserving every input tuple and the closing cycle edge
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 15, Theorem 8; proof pp. 15–16, Eqs. (22)–(25); quadratic cap and Lemma 7, pp. 13–15

import Definitions.Def_CyclicForrelation_Even_complexity
import Definitions.Def_CyclicForrelation_Even_Supplement_quadraticCap

namespace CyclicForrelation.Even.Supplement

/-- Theorem 8 (odd cycles k = 2m+1), with the uniform certificate 1/96 for the paper's Ω. -/
theorem odd_nonadaptive_lower_bound (n m : ℕ) (hm : 2 ≤ m) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    (m : ℝ) / 96 * evenScale n m ε ≤ (nonadaptiveComplexity n (2 * m + 1) ε : ℝ) := by sorry

end CyclicForrelation.Even.Supplement
