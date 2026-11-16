-- Prove2me | Theorems.Thm_BlockSSM_Supplement_theorem_14
-- name    : BlockSSM.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:07:03.154106+00:00
-- url     : https://prove2.me/theorems/87bdcd36-e32f-4d0d-a05d-f29d8a51a73c
-- title:
--   Theorem 14 — $p$-group lower bound $D_b(P)\ge p\,\alpha(P)$
-- statement:
--   Let $p$ be a prime and $P$ a finite $p$-group. For every block bound $b$,
--   $$
--   D_b(P)\ge p\,\alpha(P),\qquad \alpha(P)=\min\{d(P/A):A\trianglelefteq P,\ A\text{ abelian}\},
--   $$
--   where $d$ is the minimum number of generators.
--
--   The bound holds over every cover, and gives the lower bound $pn$ in Theorem 13 because $\alpha(E_{p,n})=n$.
--
--   Differences from the source:
--   - encoding: $d(X)$, the minimum number of generators → Mathlib's `Group.rank`; reason: the same quantity
--   - generalization: every block bound $b\ge1$ → every $b\in$ `ℕ∞`, $b=\infty$ and $b=0$ included; the inequality in `ℕ∞`; reason: $D_\infty$ is the unbounded case of Definition 2; the bound is trivial when $D_b(P)=\infty$, which covers $b=0$ for $P\neq1$ (and $\alpha(1)=0$); every source instance is a case
--   - encoding: a minimum with value $\infty$ on an empty feasible set → `sInf` in `ℕ∞`; reason: `sInf ∅ = ⊤`, and on a nonempty set of naturals `sInf` is the minimum
--   - encoding: finite covers $H$ and representations $V$ in $D_b$ → $H$ in the lowest universe, $V=\mathbb C^d$ (published `BlockSSM.coverDim`); reason: every finite group has an isomorphic copy in `Type` and every $d$-dimensional representation is isomorphic to one on $\mathbb C^d$
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 14, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_BlockSSM_coverDim
import Definitions.Def_BlockSSM_Supplement_alpha

universe u

namespace BlockSSM.Supplement

open BlockSSM

/-- **Theorem 14 (`p`-group lower bound).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 14, p.6 (PDF p.7): "For every finite
p-group P and every b, D_b(P) ≥ pα(P)."

**Formalization Note.** `p` is prime and `P` a finite `p`-group (`IsPGroup p P`); `α` is
`alpha` (minimum of `d(P/A)` over abelian normal `A`); every `b : ℕ∞`, including `b = ∞`; the
inequality is in `ℕ∞`, so it is trivial when `D_b(P) = ∞`. -/
theorem theorem_14 (p : ℕ) (hp : p.Prime) (P : Type u) [Group P] [Finite P] (hP : IsPGroup p P)
    (b : ℕ∞) :
    ((p * alpha P : ℕ) : ℕ∞) ≤ coverDim P b := by sorry

end BlockSSM.Supplement
