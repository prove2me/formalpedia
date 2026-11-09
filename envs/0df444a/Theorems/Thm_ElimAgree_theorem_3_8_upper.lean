-- Prove2me | Theorems.Thm_ElimAgree_theorem_3_8_upper
-- name    : ElimAgree.theorem_3_8_upper
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:33:08.606759+00:00
-- url     : https://prove2.me/theorems/821807ef-c32b-4f0e-b4ae-d6576da7ad13
-- title:
--   Proof of Theorem 3.8 — the protocol of cost $\lceil 2gn/(1+g)\rceil+1$
-- statement:
--   For $n\ge1$, $k\ge1$ and $0<g\le1$ there is a public-coin common-output protocol for $\mathrm{Elim}(\mathrm{DISJ}_n^k)$ of cost at most
--   $$\Big\lceil\frac{2gn}{1+g}\Big\rceil+1$$
--   whose failure probability is at most $(1-g)2^{-k}$ on every input.
--
--   This is the upper bound of Theorem 3.8 and, for small $n$, half of its $\Theta(1+gn)$ claim.
--
--   Differences from the source:
--   - generalization: n ≥ 3 (Theorem 3.8's range) → n ≥ 1; reason: the construction uses only n ≥ 1, and the Θ(1 + gn) claim needs it for n ≤ 2 (p.11); it specializes to n ≥ 3
--   - encoding: public-coin protocols that may also use private coins; cost in bits → PMF over deterministic protocol trees (private coins absorbed); cost = maximal depth over the support; reason: fixing all coins leaves a deterministic tree, and every distribution over trees is a public-coin protocol
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), proof of Theorem 3.8, pp.10–11 (PDF pp.12–13)

import Mathlib
import Definitions.Def_ElimAgree_disjAns

namespace ElimAgree

/-- The upper-bound protocol of Theorem 3.8 (proof of Theorem 3.8, pp.10–11), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission): for
`n ≥ 1`, `k ≥ 1` and `0 < g ≤ 1` there is a public-coin common-output protocol for
`Elim(DISJ_n^k)` of cost at most `⌈2gn/(1 + g)⌉ + 1` whose failure probability is at most
`(1 − g)2^{−k}` on every input.

**Formalization Note.** Bob's private coin is part of the distribution over trees. The paper's
range is `n ≥ 3`; the construction needs only `n ≥ 1`, and the `Θ(1 + gn)` claim of Theorem 3.8
uses it for `n ≤ 2`. -/
theorem theorem_3_8_upper (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (g : ℝ) (hg : 0 < g)
    (hg1 : g ≤ 1) :
    ∃ μ : PMF (ComProt n k), CostLE μ (⌈2 * g * n / (1 + g)⌉₊ + 1) ∧
      ∀ X Y : Inp n k, comErr disjAns μ X Y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k) := by sorry

end ElimAgree
