-- Prove2me | Theorems.Thm_CompactRouting_Labeled_lemma_7
-- name    : CompactRouting.Labeled.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:07:22.802176+00:00
-- url     : https://prove2.me/theorems/871071c1-492e-46bf-94db-4e545a7b31aa
-- title:
--   Lemma 7 — total table size $\tilde O(n^{1+1/k})$ bits and labels of $\tilde O(k)$ bits
-- statement:
--   Let $a,C_1,c_1,c_0$ be constants. There are constants $C,c$ such that the following holds. Let $G$ be a connected simple graph on $n$ vertices with integer edge weights in $[1,n^a]$, let $2\le k\le\lfloor\log_2 n\rfloor+1$, let $V=A_0\supseteq\cdots\supseteq A_k=\emptyset$ be a hierarchy ($A_{k-1}\ne\emptyset$) whose bunches satisfy Lemma 1's bound $|B_i(u)|\le C_1n^{1/k}(\lfloor\log_2n\rfloor+1)^{c_1}$, let $p$ be pivots by the paper's rule, and let the tree labels $L(x,T(C(w)))$ have at most $c_0(\lfloor\log_2n\rfloor+1)^2$ bits each. Then the labels and routing tables of §4.1 satisfy
--   $$\sum_{u\in V}|RT(u)|\le C\,n^{1+1/k}(\lfloor\log_2 n\rfloor+1)^c,\qquad |L(u)|\le C\,k\,(\lfloor\log_2 n\rfloor+1)^c\ \ (u\in V),$$
--   sizes in bits. This is the storage half of Theorem 1.
--
--   Differences from the source:
--   - generalization: the hierarchy of Lemma 1 and the tree labels of Lemma 4 ([TZ01], O(log² n / log log n) bits) → any hierarchy with Lemma 1's bunch bound (constants C₁, c₁) and any tree labels of at most c₀(⌊log₂ n⌋+1)² bits; C, c depend on a, C₁, c₁, c₀; reason: Lemma 1's hierarchy and Lemma 4's labels satisfy these bounds, so the statement specializes to the paper's
--   - reading: Õ bounds with the proof's 'and k ≤ log n' → hypothesis k ≤ ⌊log₂ n⌋ + 1; reason: the proof uses k ≤ log n; it is the paper's tacit range for Õ (see INSIGHTS.yaml I1); ⌊log₂ n⌋+1 admits every k ≤ log₂ n
--   - encoding: sizes in words of O(log n) bits, weights 'polynomially bounded integers' (fn. 5) → sizes in bits of a fixed self-delimiting encoding, integer weights in [1, n^a], heights stored as ⌊h_i(v)⌋; reason: a word is Θ(log n) bits, absorbed in the polylog; ⌊h⌋ = h for integer weights
--   - encoding: pivots p(u, X) = 'the vertex of X closest to u' and the hierarchy V = A_0 ⊇ ⋯ ⊇ A_k = ∅ → `IsPivots A p` (any closest vertex, the page's tie rule) and the published `Hierarchy`, which includes A_{k−1} ≠ ∅; reason: p_{k−1}(u) = p(u, A_{k−1}) exists only if A_{k−1} ≠ ∅; the condition excludes only cases where the page's pivots are undefined
--   - encoding: G = (V, E, ℓ) connected undirected with positive weights, vertices with identifiers 1..n → published edge-list `TZLevelsADO.Graph` on `Fin n` with hypotheses `IsSimple`, `Connected` (positive weights follow from `IntWeights`); reason: Lean convention; same instances
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 12, Lemma 7

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Scheme
import Definitions.Def_CompactRouting_Labeled_Tables

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 12, Lemma 7:
"∑_{u∈V} |RT(u)| = Õ(n^{1+1/k}), and |L(u)| = Õ(k) for every u ∈ V."
`RT(u)` and `L(u)` are the §4.1 tables and labels (`tableOf`, `labelOf`), sizes in bits, built
from any hierarchy whose bunches obey Lemma 1's bound `|B_i(u)| ≤ C₁ n^{1/k}(⌊log₂ n⌋+1)^{c₁}`,
the pivots, and any tree labels of at most `c₀(⌊log₂ n⌋+1)²` bits; weights are integers in
`[1, n^a]` (footnote 5); `k ≤ ⌊log₂ n⌋ + 1` (the proof's "k ≤ log n"). -/
theorem lemma_7 :
    ∀ a C₁ c₁ c₀ : ℕ, ∃ C c : ℕ, ∀ (G : Graph) (k : ℕ), IsSimple G → G.Connected →
      IntWeights G a → 2 ≤ k → k ≤ Nat.log 2 G.n + 1 →
      ∀ A : Hierarchy G k,
        (∀ i < k, ∀ u : Fin G.n,
          ((bunchAt A i u).card : ℝ) ≤ C₁ * (G.n : ℝ) ^ (1 / (k : ℝ)) * ((Nat.log 2 G.n : ℝ) + 1) ^ c₁) →
      ∀ p : ℕ → Fin G.n → Fin G.n, IsPivots A p →
      ∀ tl : Fin G.n → Fin G.n → List Bool,
        (∀ w x : Fin G.n, ((tl w x).length : ℝ) ≤ c₀ * ((Nat.log 2 G.n : ℝ) + 1) ^ 2) →
        (∑ u : Fin G.n, ((tableOf A p tl u).size : ℝ)) ≤
            C * (G.n : ℝ) ^ (1 + 1 / (k : ℝ)) * ((Nat.log 2 G.n : ℝ) + 1) ^ c ∧
          ∀ u : Fin G.n, ((labelOf A p tl u).size : ℝ) ≤ C * k * ((Nat.log 2 G.n : ℝ) + 1) ^ c := by sorry

end CompactRouting.Labeled
