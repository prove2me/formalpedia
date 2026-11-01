-- Prove2me | Theorems.Thm_FairFlows_decMin_iff_narrow_box
-- name    : FairFlows.decMin_iff_narrow_box
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:15:16.996679+00:00
-- url     : https://prove2.me/theorems/43de5320-5d19-4d04-9398-049f15c23a30
-- title:
--   Theorem 2.1 — the integral $F$-dec-min feasible flows are the integral flows of a box narrow on $F$
-- statement:
--   Let $D=(V,A)$ be a digraph with integer-valued lower and upper bound functions $f:A\to\mathbb Z\cup\{-\infty\}$ and $g:A\to\mathbb Z\cup\{+\infty\}$, $f\le g$. Let $m:V\to\mathbb Z$ satisfy $\widetilde m(V)=0$ and suppose there exists an $(f,g)$-bounded (real) $m$-flow. Let $F\subseteq A$ be a set of edges on which both $f$ and $g$ are finite. Then there is a pair $(f^*,g^*)$ of integer-valued functions on $A$, with
--   $$f\le f^*\le g^*\le g$$
--   (allowing $f^*(e)=-\infty$ and $g^*(e)=+\infty$ for $e\in A-F$), such that an integral $(f,g)$-bounded $m$-flow $z$ is decreasingly minimal on $F$ if and only if $z$ is an integral $(f^*,g^*)$-bounded $m$-flow. Moreover the box $T(f^*,g^*)$ is narrow on $F$:
--   $$0\le g^*(e)-f^*(e)\le 1\qquad\text{for every } e\in F.$$
--
--   The theorem describes all fair (decreasingly minimal) integral feasible flows as the integral points of a single box intersected with the flow polyhedron, so that, for instance, a cheapest $F$-dec-min flow is an ordinary minimum-cost flow problem with bounds $(f^*,g^*)$.
--
--   **Formalization Note** The hypothesis is a real feasible flow ($Q\neq\emptyset$), as printed; decreasing minimality is taken among the integral feasible flows.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: bounds f : A → ℤ∪{−∞}, g : A → ℤ∪{+∞} → WithBot ℤ / WithTop ℤ, every comparison written termwise without ∞ arithmetic; reason: Lean convention; same instances
--   - encoding: decreasingly minimal on F → no member of the set has a non-increasingly sorted value list on F that is lexicographically smaller (List.Lex (· < ·)); reason: Lean convention; this is the paper's definition
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Theorem 2.1, p.6

import Mathlib
import Definitions.Def_FairFlows_Network
import Definitions.Def_FairFlows_DecMin

set_option autoImplicit false

namespace FairFlows

/-- Theorem 2.1 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.6), the main theorem. Let `D = (V, A)` be a digraph with
integer-valued bounds `f : A → ℤ ∪ {−∞}`, `g : A → ℤ ∪ {+∞}`, `f ≤ g`; let `m : V → ℤ` with
`m̃(V) = 0` admit an `(f, g)`-bounded `m`-flow; and let `F ⊆ A` be a set of edges on which `f`
and `g` are finite. There is a pair `(f*, g*)` of integer-valued functions on `A` with
`f ≤ f* ≤ g* ≤ g` (allowing `f*(e) = −∞`, `g*(e) = +∞` for `e ∈ A − F`) such that an integral
`(f, g)`-bounded `m`-flow `z` is decreasingly minimal on `F` if and only if `z` is an integral
`(f*, g*)`-bounded `m`-flow; moreover `T(f*, g*)` is narrow on `F`: `0 ≤ g*(e) − f*(e) ≤ 1` for
every `e ∈ F`.

**Formalization Note** The hypothesis is a real `(f, g)`-bounded `m`-flow (`Q ≠ ∅`), as printed;
decreasing minimality is among the integral flows `Q⃛(f, g; m)`. Digraphs may have parallel
edges and loops; no connectivity is assumed. -/
theorem decMin_iff_narrow_box {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ)
    (hfg : BoundsLE f g) (hm : demandSum m Finset.univ = 0)
    (hQ : (feasFlows D f g m).Nonempty)
    (F : Finset A) (hF : ∀ e ∈ F, f e ≠ ⊥ ∧ g e ≠ ⊤) :
    ∃ (fs : A → WithBot ℤ) (gs : A → WithTop ℤ),
      f ≤ fs ∧ BoundsLE fs gs ∧ gs ≤ g ∧ (∀ e ∈ F, NarrowAt fs gs e) ∧
      ∀ z ∈ intFlows D f g m,
        (IsDecMinOn (intFlows D f g m) F z ↔ z ∈ intFlows D fs gs m) := by sorry

end FairFlows
