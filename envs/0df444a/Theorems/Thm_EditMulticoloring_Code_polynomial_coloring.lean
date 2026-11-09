-- Prove2me | Theorems.Thm_EditMulticoloring_Code_polynomial_coloring
-- name    : EditMulticoloring.Code.polynomial_coloring
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T18:49:15.737131+00:00
-- url     : https://prove2.me/theorems/419541ad-6b40-4bbc-b826-c7193b7a3de1
-- title:
--   Lemma 7 — Coloring by the first separating point
-- statement:
--   Let $G$ be any finite simple graph, let integers $r,K\ge1$ bound its degree and identifier bit length, and let $\mathrm{id}:V\to\{0,\ldots,2^K-1\}$ be injective. Put $Q=2^{\lceil\log_2(rK+1)\rceil}$, and fix a field of order $Q$ with a bijection to the ordered labels $\{0,\ldots,Q-1\}$. Build the degree-less-than-$K$ identifier polynomial $g_v$ from the $K$ base-$Q$ digits, including leading zeros. Then each vertex has a separating point, its first such point $\alpha_v$ does separate it, and
--
--   $$f(v)=Q\,\mathrm{label}(\alpha_v)+\mathrm{label}(g_v(\alpha_v))<Q^2,\qquad f(u)\ne f(v)\ \text{for every edge }uv.$$
--
--   This supplies the explicit proper coloring used before prime compression; existence of separating points is a conclusion.
--
--   Differences from the source: none.
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), Lemma 7 and Definition 6, printed p. 6 (PDF p. 7); proof printed p. 7 (PDF p. 8); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Definitions.Def_EditMulticoloring_Code_Graph

namespace EditMulticoloring.Code

theorem polynomial_coloring {V F : Type} [Fintype V] [Field F]
    (G : SimpleGraph V) (r K : ℕ) (hr : 1 ≤ r) (hK : 1 ≤ K)
    (degree : ∀ v, (neighbors G v).card ≤ r)
    (id : V → ℕ) (hid : Function.Injective id) (range : ∀ v, id v < 2 ^ K)
    (e : F ≃ Fin (fieldSize r K)) :
    (∀ v, ∃ a : F, Separates G e K id v a) ∧
    (∀ v, Separates G e K id v (firstSeparating G e K id v)) ∧
    (∀ v, polynomialColor G e K id v < (fieldSize r K) ^ 2) ∧
    (∀ u v, G.Adj u v → polynomialColor G e K id u ≠ polynomialColor G e K id v)
    := by sorry

end EditMulticoloring.Code
