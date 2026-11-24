-- Prove2me | Theorems.Thm_BB6Kit_rows_counts
-- name    : BB6Kit.rows_counts
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-24T07:20:51.06083+00:00
-- url     : https://prove2.me/theorems/0d8cdd71-7c8c-4411-9b34-d6082e83ff41
-- title:
--   Row sums of the kit: $\sum k_i=\sum m_i=N(K-1)/3$ and $\sum\log(k_i!\,m_i!)=2L\log\prod_k(k!)^{K-k}$
-- statement:
--   **Lemma.** Let $K\ge3$, $L\ge5$, $N=K(K+1)L/2$, and let the rows $(k_i,m_i,\ell_i)$ be $N$ distinct elements of $\{(k,m,\ell):k+m\le K-1,\ \ell<L\}$. Since there are exactly $N$ such triples, they enumerate the set. Then $$\sum_i k_i=\sum_i m_i=\frac{N(K-1)}{3},\qquad \sum_i\bigl(\log k_i!+\log m_i!\bigr)=2L\log\prod_{k=1}^{K-1}(k!)^{K-k}.$$
--
--   These are the identity (3.16) and the factorial count behind the quantity $b$ of (2.5) in the Mignotte–Voutier kit. Each value $k$ occurs $(K-k)L$ times, and $\sum_{k<K}k(K-k)=K(K-1)(K+1)/6$.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, eq. (3.16) and the definition (2.5) of b.

import Mathlib
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem rows_counts (K L N : ℕ) (kml : Fin N → ℕ × ℕ × ℕ) (hK : 3 ≤ K) (hL : 5 ≤ L)
    (hN : N = K * (K + 1) * L / 2) (hrows : BB6Kit.RowsOK K L N kml) :
    (∑ i, ((kml i).1 : ℝ)) = (N : ℝ) * ((K : ℝ) - 1) / 3 ∧
    (∑ i, ((kml i).2.1 : ℝ)) = (N : ℝ) * ((K : ℝ) - 1) / 3 ∧
    ∑ i, (Real.log ((kml i).1.factorial : ℝ) + Real.log ((kml i).2.1.factorial : ℝ)) =
      2 * (L : ℝ) * Real.log (∏ k ∈ Finset.Ico 1 K, ((k.factorial : ℝ) ^ (K - k))) := by
  sorry
end BB6Kit
