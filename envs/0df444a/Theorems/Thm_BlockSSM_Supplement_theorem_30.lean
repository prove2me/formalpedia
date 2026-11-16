-- Prove2me | Theorems.Thm_BlockSSM_Supplement_theorem_30
-- name    : BlockSSM.Supplement.theorem_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:08:59.687198+00:00
-- url     : https://prove2.me/theorems/b32c0824-e6db-428e-8ec7-0008f3316f71
-- title:
--   Theorem 30 — characteristic-zero fields, $n_{b,F}(G)=D_{b,F}(G)$
-- statement:
--   Let $F$ be any field of characteristic zero (not necessarily algebraically closed) and $G$ a finite group. Then
--   $$
--   n_{b,F}(G)=D_{b,F}(G),
--   $$
--   where all affine maps of the tracker, all representations of the cover, and all irreducible constituents are taken over $F$. Both sides are $\infty$ when infeasible.
--
--   The exact dimension theorem therefore holds over $\mathbb Q$, $\mathbb R$ and every other characteristic-zero field, where the threshold may differ from the complex one.
--
--   Differences from the source:
--   - generalization: an integer block bound $b$ → $b\in\mathbb N\cup\{\infty\}$ (`ℕ∞`), every value including $b=\infty$; reason: every integer bound is a case through the cast and $b=\infty$ is the unbounded case ($D_\infty$ of Definition 2); the argument is the same
--   - encoding: Definitions 1 and 2 over $F$ → the field-parametric `FTracker`, `trackerDimF`, `coverDimF`, with $V=F^d$ and $H$ in the lowest universe; reason: the same definitions with $\mathbb C$ replaced by $F$
--   - encoding: irreducible constituents over $F$ → $F$-irreducible subrepresentations; reason: Maschke's theorem holds over a field of characteristic zero, so every constituent is isomorphic to a subrepresentation
--   - encoding: a minimum with value $\infty$ on an empty feasible set → `sInf` in `ℕ∞`; reason: `sInf ∅ = ⊤`, and on a nonempty set of naturals `sInf` is the minimum
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 30, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_BlockSSM_Supplement_FTracker
import Definitions.Def_BlockSSM_Supplement_coverDimF

universe u v

namespace BlockSSM.Supplement

/-- **Theorem 30 (characteristic-zero fields).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 30, p.18 (PDF p.19): "For any field
F of characteristic zero, n_{b,F}(G) = D_{b,F}(G), where all affine maps, representations, and
irreducible constituents are taken over F."

**Formalization Note.** `F` is any field with `CharZero F` (not assumed algebraically closed, in
any universe), `G` a finite group, `b : ℕ∞`. `n_{b,F}` is `trackerDimF` and `D_{b,F}` is
`coverDimF`; both are `⊤` when infeasible. -/
theorem theorem_30 (F : Type v) [Field F] [CharZero F] (G : Type u) [Group G] [Finite G]
    (b : ℕ∞) : trackerDimF F G b = coverDimF F G b := by sorry

end BlockSSM.Supplement
