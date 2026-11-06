-- Prove2me | Theorems.Thm_AnytimeAdaVR_eq_46
-- name    : AnytimeAdaVR.eq_46
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:37.010234+00:00
-- url     : https://prove2.me/theorems/7f9353a0-e3e5-49db-b67e-304f42845240
-- title:
--   App. C.6 (46) — at most $16\,b_s$ queries reuse a failed block's label
-- statement:
--   Let $p=2$ for S and $p=1$ for M, and let $(a_j,b_j)$ follow Table 2 from $(1,2)$ for any counts $m_j\le b_j$. A block of an S path costs $b$ queries and a block of an M path $2b-1$. Suppose block $s$ fails ($m_s<b_s/2$). The blocks whose label is $Y_s$ are the blocks $j>s$ with $b_j>2$ and no failed block strictly between $s$ and $j$. Their total query cost, including an unfinished final block, is at most
--   $$
--   2\sum_{k=0}^\infty 2^{2/p}b_s2^{-2k/p}=\frac{2\cdot2^{2/p}}{1-2^{-2/p}}\,b_s\le 16\,b_s .
--   $$
--   This pathwise reuse bound is applied before taking expectations in the proof of Proposition C.1.
--
--   **Formalization Note** Stated for every horizon $J$: the cost of such blocks $j$ with $s<j\le J$ is at most $16b_s$, which covers an unfinished final block (its full cost is counted).
--
--   Differences from the source:
--   - generalization: the path's own counts m_j → every sequence of counts m with m_j ≤ b_j; reason: the path's counts are one such sequence, so the statement specializes to the path
--   - encoding: blocks indexed j = 1, 2, … with a_1 = 1, b_1 = 2 → 0-based block index j = 0, 1, … (paramSeq / smState at j is the paper's block j + 1); reason: index shift only
--   - encoding: the number of queries with b > 2 that can ever receive label Y_s, including an unfinished final block → for every J, the total cost (b_j for S, 2b_j − 1 for M) of the blocks s < j ≤ J with b_j > 2 and no failed block strictly between s and j; reason: these are exactly the blocks labelled Y_s; counting each block's full cost covers an unfinished block
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. C.6, eq. (46), p.23

import Mathlib
import Definitions.Def_AnytimeAdaVR_paramSeq

namespace AnytimeAdaVR

/-- **App. C.6, eq. (46): the reuse count of a failed block's label.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. C.6, p.23:
"After this failure, the next block has length 2^{2/p}b_s. Until the next failed block finishes, the
lengths greater than two form a decreasing geometric sequence. Every block has query cost between b
and 2b. The number of queries with b > 2 that can ever receive label Y_s is therefore at most
2 Σ_{k=0}^∞ 2^{2/p} b_s 2^{−2k/p} = 2·2^{2/p}/(1 − 2^{−2/p}) b_s ≤ 16 b_s. This count includes an
unfinished final block."

Let block `s` fail (`m_s < b_s/2`). The blocks labelled `Y_s` are the blocks `j > s` with
`b_j > 2` and no failed block strictly between `s` and `j`. For every `J`, their total query cost
(`b_j` for S, `2b_j − 1` for M) over `s < j ≤ J` is at most `16 b_s`.

**Formalization Note.** Blocks are 0-based. The bound is deterministic and stated for every
sequence of counts `m_j ≤ b_j` (the path's counts are one), with `(a_j, b_j) = paramSeq k m j`.
Partial sums up to every `J` cover the unfinished final block (its full cost is counted). -/
theorem eq_46 (k : SMKind) (m : ℕ → ℕ) (hm : ∀ j, m j ≤ (paramSeq k m j).2) (s : ℕ)
    (hs : 2 * m s < (paramSeq k m s).2) (J : ℕ) :
    let b : ℕ → ℕ := fun j => (paramSeq k m j).2
    let cost : ℕ → ℕ := fun j =>
      match k with
      | .S => b j
      | .M => 2 * b j - 1
    ∑ j ∈ (Finset.Ioc s J).filter (fun j => 2 < b j ∧ ∀ i ∈ Finset.Ioo s j, b i ≤ 2 * m i),
        cost j ≤ 16 * b s := by sorry

end AnytimeAdaVR
