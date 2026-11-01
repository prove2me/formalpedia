-- Prove2me | Theorems.Thm_ConstrainedTrading_mnatConcave_sum_disjoint
-- name    : ConstrainedTrading.mnatConcave_sum_disjoint
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:33.365375+00:00
-- url     : https://prove2.me/theorems/f8c7d057-1c2a-4036-83d2-bd471ef6fc75
-- title:
--   §2.2 — a sum of M$^\sharp$-concave functions of disjoint blocks of variables is M$^\sharp$-concave
-- statement:
--   Let the coordinates $E$ be partitioned into blocks $E_i$ ($i\in\iota$, $\iota$ finite), and for each $i$ let $f_i:\mathbb Z^{E_i}\to\mathbb R\cup\{-\infty\}$ be M$^\sharp$-concave. Then
--   $$
--   f(y)=\sum_{i\in\iota}f_i\bigl(y|_{E_i}\bigr)\qquad(y\in\mathbb Z^E)
--   $$
--   is M$^\sharp$-concave.
--
--   The paper uses this for the aggregate valuation $f(y)=\sum_i w_i(y^i)$ of a trading network (§2.2) and, in the proof of Theorem 3.1, for $\sum_i w_i^+$ over the agents' outgoing arcs.
--
--   **Formalization Note** The blocks are the fibres of a map $g:E\to\iota$ and $y|_{E_i}$ is the restriction to the subtype `{e // g e = i}`; the sum is in `WithBot ℝ`.
--
--   Differences from the source:
--
--   - encoding: f(y) = Σᵢ wᵢ(yⁱ) with the arguments yⁱ disjoint → blocks = fibres of g : E → ι, f_i applied to the restriction of y to {e // g e = i}; reason: a partition of the variables into disjoint blocks; same instances
--   - reading: M♯-concave f : ℤ^E → R, exchange 'for all x, y ∈ B' with B unnamed (Def 2.7, p.4; p.5) → f : ℤ^E → ℝ ∪ {−∞}, exchange for x, y ∈ dom f = {z : f z ≠ −∞}; reason: the paper's valuations take values in ℝ ∪ {−∞} (p.3, footnote 3) and p.5 defines dom f; the real-valued case is dom f = ℤ^E
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, §2.2, p.5 ("Note, f(y) is also M♯ concave because the argument of each wi are disjoint"); proof of Theorem 3.1, p.8

import Mathlib
import Definitions.Def_ConstrainedTrading_MNatConcave

namespace ConstrainedTrading

/-- **Sums over disjoint blocks of variables are M♯-concave** (Kizilkale–Vohra, *Constrained
Trading Networks*, arXiv:2008.09757v1, §2.2, p.5: "Suppose each agent's valuation function,
wᵢ is M♯-concave and let f(y) = Σᵢ wᵢ(yⁱ). Note, f(y) is also M♯ concave because the argument
of each wᵢ are disjoint"). Let the coordinates `E` be partitioned into blocks by `g : E → ι`,
with `ι` finite, and let `fᵢ : ℤ^{g⁻¹(i)} → ℝ ∪ {−∞}` be M♯-concave for every `i`. Then
`y ↦ Σᵢ fᵢ(y|_{g⁻¹(i)})` is M♯-concave on `ℤ^E`.

**Formalization Note** Block `i` is the subtype `{e // g e = i}`, and `y|_{g⁻¹(i)}` is
`fun e => y e.1`. The sum is taken in `WithBot ℝ`. In the proof of Theorem 3.1 (p.8) this is
used with `g` the seller map and `fᵢ = w⁺ᵢ`. -/
theorem mnatConcave_sum_disjoint {E ι : Type*} [Fintype ι] [DecidableEq E] [DecidableEq ι]
    (g : E → ι) (f : (i : ι) → ({e // g e = i} → ℤ) → WithBot ℝ)
    (hf : ∀ i, MNatConcave (f i)) :
    MNatConcave (fun y : E → ℤ => ∑ i, f i (fun e : {e // g e = i} => y e.1)) := by sorry

end ConstrainedTrading
