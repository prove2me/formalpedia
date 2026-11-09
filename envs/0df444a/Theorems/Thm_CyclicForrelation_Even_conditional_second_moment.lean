-- Prove2me | Theorems.Thm_CyclicForrelation_Even_conditional_second_moment
-- name    : CyclicForrelation.Even.conditional_second_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:58.685113+00:00
-- url     : https://prove2.me/theorems/caecf9ec-ef8a-4ecc-92b9-a10995eedf95
-- title:
--   Claim 11 — conditional second moment with the equality clause
-- statement:
--   Let $n\in\mathbb N$, $N=2^n$, and let $k\ge4$ be even. Fix arbitrary sign functions $f_1,\ldots,f_k$ on $G$, and let $\varnothing\ne S\subseteq[k]$ have cardinality $r$. For the cyclic kernel and normalized conditional moment defined above,
--   $$\|h_S\|_2^2\le\begin{cases}N^{r-k+1},&S\text{ is independent},\\N^{r-k},&S\text{ is not independent}.\end{cases}$$
--   In the second case equality holds:
--   $$S\text{ not independent}\quad\Longrightarrow\quad\|h_S\|_2^2=N^{r-k}.$$
--   The statement includes every nonempty overlap pattern, without an input promise or restrictions on the sign functions. It is the moment estimate used to control the sampling estimator.
--
--   Differences from the source:
--   - encoding: one-based sign-function tuples on the binary cube → zero-based finite indices and Boolean signs interpreted as real ±1; reason: these are bijective encodings, with the closing cycle edge and every input tuple preserved
--   - encoding: a piecewise upper bound followed by equality in its second case → an implication for the independent case and an equality implication for the other case; reason: the two implications are logically equivalent to the complete piecewise assertion, including the equality clause
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 17, Claim 11 (even k≥4 inherited from Theorem 10)

import Definitions.Def_CyclicForrelation_Even_sampling

namespace CyclicForrelation.Even

/-- Claim 11, including equality whenever S contains an edge of the cycle. -/
theorem conditional_second_moment (n k : ℕ) (hk : 4 ≤ k) (heven : Even k)
    (f : OracleTuple n k) (S : Finset (Fin k)) (hS : S.Nonempty) :
    (CycleIndependent S → conditionalSecondMoment f S ≤
      (cubeSize n : ℝ) ^ ((S.card : ℝ) - (k : ℝ) + 1)) ∧
    (¬ CycleIndependent S → conditionalSecondMoment f S =
      (cubeSize n : ℝ) ^ ((S.card : ℝ) - (k : ℝ))) := by sorry

end CyclicForrelation.Even
