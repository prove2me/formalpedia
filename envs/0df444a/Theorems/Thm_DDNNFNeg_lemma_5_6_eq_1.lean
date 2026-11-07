-- Prove2me | Theorems.Thm_DDNNFNeg_lemma_5_6_eq_1
-- name    : DDNNFNeg.lemma_5_6_eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:37.08753+00:00
-- url     : https://prove2.me/theorems/9668011b-e86b-4c45-8d14-8190ff46be1a
-- title:
--   Eq. (1), proof of Lemma 5.6 — $\mathbb P[Y_i = 1 \mid Y_1, \dots, Y_{i-1}] \ge 1/16$
-- statement:
--   Let $G$ be a 3-regular graph on $[n]$, $e_1, \dots, e_k$ edges of $G$ with pairwise disjoint neighbourhoods, $X$ the indicator vector of a uniformly random independent set of $G$, and $Y_i$ the indicator that $e_i$ is free (all of $D_i = N(e_i) \setminus e_i$ is set to $0$). For every $i$ and every $y_1, \dots, y_{i-1}$,
--   $$
--   \mathbb P[Y_i = 1 \mid Y_1 = y_1, \dots, Y_{i-1} = y_{i-1}] \ge \frac{1}{16}.
--   $$
--
--   **Formalization Note** With $S$ the set of independent sets $x$ with $Y_j(x) = y_j$ for all $j < i$, the bound is written as $|S| \le 16 \cdot |\{x \in S : Y_i(x) = 1\}|$, which is the conditional bound when $S \neq \emptyset$ and trivial when $S = \emptyset$.
--
--   Differences from the source:
--   - generalization: the crossing, same-colour edges of Lemma 5.4 in the expander G of §5.2 → any edges with pairwise disjoint neighbourhoods in any 3-regular graph; reason: crossing, colour and expansion are not used; the paper's edges are a special case
--   - encoding: P[Yᵢ = 1 | Y₁ = y₁, …, Y_{i−1} = y_{i−1}] ≥ 1/16 for conditions of positive probability → |S| ≤ 16·|{x ∈ S : Yᵢ(x) = 1}| for every prefix y; reason: the uniform law on independent sets; an empty S gives 0 ≤ 0
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), proof of Lemma 5.6, Eq. (1), p.14

import Mathlib
import Definitions.Def_DDNNFNeg_IsFree
import Definitions.Def_DDNNFNeg_indepSets

namespace DDNNFNeg

/-- **Eq. (1)**, proof of Lemma 5.6 (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.14): for a uniformly random independent set `X` of a
3-regular graph `G` and edges `e₁, …, e_k` with pairwise disjoint neighbourhoods, let `Yᵢ` be the
indicator that `eᵢ` is free. Then for every `i` and every `y₁, …, y_{i−1}`,
`P[Yᵢ = 1 | Y₁ = y₁, …, Y_{i−1} = y_{i−1}] ≥ 1/16`.

**Formalization Note** With `S` the set of independent sets `x` with `Yⱼ(x) = yⱼ` for all
`j < i`, the bound is written in counting form `|S| ≤ 16 · |{x ∈ S : Yᵢ(x) = 1}|`, which is the
conditional probability bound when `S ≠ ∅` (the paper conditions only on events of positive
probability) and is trivially true when `S = ∅`. The values `yⱼ` for `j ≥ i` are ignored. The
edges need not be crossing nor of one colour, and no colouring or expansion is assumed (a
generalization). -/
theorem lemma_5_6_eq_1 {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (u v : Fin k → Fin n) (hadj : ∀ i, G.Adj (u i) (v i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (edgeNbhd G s(u i, v i)) (edgeNbhd G s(u j, v j)))
    (i : Fin k) (y : Fin k → Bool) :
    ((indepSets G).filter (fun x => ∀ j < i, decide (IsFree G s(u j, v j) x) = y j)).card ≤
      16 * ((indepSets G).filter (fun x =>
        (∀ j < i, decide (IsFree G s(u j, v j) x) = y j) ∧ IsFree G s(u i, v i) x)).card := by sorry

end DDNNFNeg
