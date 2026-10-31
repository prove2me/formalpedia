-- Prove2me | Theorems.Thm_BimatrixStableSet_theorem_4
-- name    : BimatrixStableSet.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:11.190388+00:00
-- url     : https://prove2.me/theorems/ac82b581-cb0d-4be4-9f8b-aba2d46cb815
-- title:
--   Theorem 4 (facet-stable-set bound) — equilibrium vertices in a facet lie in a stable pair
-- statement:
--   Let $m\ge2$, and consider a non-degenerate $m\times n$ game $(A,B)$ with positive payoff matrices and best-response polytopes $P$ and $Q$. Let $F$ be a facet of $P$ with label $\ell$, and $G_F$ the graph of $F$. Then the equilibrium vertices in $G_F$ are contained in two disjoint stable sets in $G_F$ of equal size.
--
--   So the stable-set bound of a facet $F$ bounds the equilibria with an equilibrium vertex in $F$, which is how obstruction vertices of the facets arise.
--
--   Differences from the source:
--   - encoding: labels in $[m+n]$ → the type `Fin m ⊕ Fin n`, with label $i\le m$ as `Sum.inl` and label $m+j$ as `Sum.inr`; reason: same labels, zero-based
--   - encoding: a facet $F$ with label $\ell$ → $F=P_\ell=\{x\in P\mid x\text{ has label }\ell\}$, with the hypothesis that it is a facet; reason: p.8: every binding inequality of a non-degenerate game defines a facet with its own label
--   - encoding: positive payoff matrices → $0<A_{ij}$ and $0<B_{ij}$ for all $i,j$; reason: same condition
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Theorem 4, pp.12–13

import Mathlib
import Definitions.Def_BimatrixStableSet_BestResponse
import Definitions.Def_BimatrixStableSet_StableSets

namespace BimatrixStableSet

variable {m n : ℕ}

/-- Theorem 4 (Facet-stable-set bound), pp.12–13 (Ickstadt, Theobald, von Stengel,
arXiv:2411.12385v3): let `m ≥ 2` and consider a non-degenerate `m × n` game `(A, B)` with positive
payoff matrices and best-response polytopes `P` and `Q`. Consider a facet `F` with label `ℓ` of `P`
and the graph `G_F` of `F`. Then the equilibrium vertices in `G_F` are contained in two disjoint
stable sets in `G_F` of equal size.

**Formalization Note.** The facet with label `ℓ` is `{x ∈ P | x has label ℓ}`, and that it is a facet
is a hypothesis. The label `ℓ` may belong to either player. Boundedness of `P`, `Q` is the paper's
"best-response polytopes"; positivity alone does not give it for `n = 0`. -/
theorem theorem_4 (hm : 2 ≤ m) (A B : Matrix (Fin m) (Fin n) ℝ)
    (hPQ : HasBestResponsePolytopes A B) (hAB : IsNondegenerate A B)
    (hpos : ∀ i j, 0 < A i j ∧ 0 < B i j) (l : Fin m ⊕ Fin n)
    (hl : (bestResponseP B).IsFacetOf ((bestResponseP B).face {l}) (bestResponseP B).carrier) :
    ∃ S₁ S₂ : Finset ((bestResponseP B).vertices ((bestResponseP B).face {l})),
      IsStablePair ((bestResponseP B).graph ((bestResponseP B).face {l})) S₁ S₂ ∧
      ∀ v : (bestResponseP B).vertices ((bestResponseP B).face {l}),
        IsEquilibriumVertex A B v → v ∈ S₁ ∨ v ∈ S₂ := by sorry

end BimatrixStableSet
