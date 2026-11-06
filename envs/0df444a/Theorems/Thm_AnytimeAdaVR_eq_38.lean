-- Prove2me | Theorems.Thm_AnytimeAdaVR_eq_38
-- name    : AnytimeAdaVR.eq_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:32.984049+00:00
-- url     : https://prove2.me/theorems/1eb142b3-4f3e-4fed-90e4-7ecff782c456
-- title:
--   App. C.1 (38) — the potential $H_J\le 9\log a_{J+1}+2$
-- statement:
--   Let $p=2$ for S and $p=1$ for M. For any counts $m_1,m_2,\dots$ with $m_j\le b_j$, let $(a_j,b_j)$ be generated from $(a_1,b_1)=(1,2)$ by Table 2, and put
--   $$
--   u_j=\frac{(2/b_j)^{p/2}}{a_j}.
--   $$
--   Then for every $J\ge0$,
--   $$
--   H_J:=\sum_{j=1}^J u_j\le 9\log a_{J+1}+2(u_1-u_{J+1})\le 9\log a_{J+1}+2 .
--   $$
--   This deterministic potential bound reduces the control of the block parameters to the growth of the scale $a_j$.
--
--   **Formalization Note** Blocks are indexed from $0$, so the sum is over the first $J$ blocks and $a_{J+1}$ is the scale after them.
--
--   Differences from the source:
--   - generalization: the path's own counts m_j → every sequence of counts m with m_j ≤ b_j; reason: the path's counts are one such sequence, so the statement specializes to the path
--   - encoding: blocks indexed j = 1, 2, … with a_1 = 1, b_1 = 2 → 0-based block index j = 0, 1, … (paramSeq / smState at j is the paper's block j + 1); reason: index shift only
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. C.1, eq. (38), p.20; definitions p.19

import Mathlib
import Definitions.Def_AnytimeAdaVR_paramSeq

namespace AnytimeAdaVR

/-- **App. C.1, eq. (38): the block-parameter potential.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. C.1, pp.19–20: with
`u_j = (2/b_j)^{p/2}/a_j` (`p = 2` for S, `p = 1` for M), "Summing over either type of block and
using u_1 = a_1 = 1 gives H_J := Σ_{j=1}^J u_j ≤ 9 log a_{J+1} + 2(u_1 − u_{J+1}) ≤ 9 log a_{J+1} + 2."

For every sequence of large-estimate counts `m_j ≤ b_j`, the parameters `(a_j, b_j)` generated from
`(1, 2)` by Table 2 satisfy both inequalities of (38), for every `J`.

**Formalization Note.** Blocks are 0-based: `paramSeq k m j` is the paper's `(a_{j+1}, b_{j+1})`, so
the paper's `H_J` is the sum over `j < J` and its `a_{J+1}` is `(paramSeq k m J).1`. The bound is
deterministic and is stated for every count sequence; the path's counts are one of them.
`(2/b)^{p/2}` is `2/b` for S and `√(2/b)` for M. -/
theorem eq_38 (k : SMKind) (m : ℕ → ℕ) (hm : ∀ j, m j ≤ (paramSeq k m j).2) (J : ℕ) :
    let u : ℕ → ℝ := fun j =>
      (match k with
        | .S => 2 / ((paramSeq k m j).2 : ℝ)
        | .M => Real.sqrt (2 / ((paramSeq k m j).2 : ℝ))) / (paramSeq k m j).1
    (∑ j ∈ Finset.range J, u j ≤ 9 * Real.log (paramSeq k m J).1 + 2 * (u 0 - u J)) ∧
    9 * Real.log (paramSeq k m J).1 + 2 * (u 0 - u J) ≤ 9 * Real.log (paramSeq k m J).1 + 2 := by sorry

end AnytimeAdaVR
