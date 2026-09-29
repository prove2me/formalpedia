-- Prove2me | Theorems.Thm_ApproxCliqueWidth_Certificate_interpolation_properties
-- name    : ApproxCliqueWidth.Certificate.interpolation_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:31:34.114294+00:00
-- url     : https://prove2.me/theorems/c9a81fae-926c-4a30-bc69-d2c9eaee8754
-- title:
--   Proposition 4.1 — basic properties of an interpolation
-- statement:
--   Let $V$ be a finite set and $f : 2^V \to \mathbb{Z}$ a submodular function such that $f(\emptyset) \le f(X)$ for all $X \subseteq V$, and let $f^*$ be an interpolation of $f$. Then:
--
--   1. for every disjoint pair $(X, Y)$,
--   $$f^*(X, Y) \le \min_{X \subseteq Z \subseteq V \setminus Y} f(Z);$$
--   2. $f^*(\emptyset, Y) = f(\emptyset)$ for every $Y \subseteq V$;
--   3. if $f(\{v\}) - f(\emptyset) \le 1$ for every $v \in V$, then for every fixed $B \subseteq V$ the function $X \mapsto f^*(X, B) - f(\emptyset)$ is the rank function of a matroid on $V \setminus B$.
--
--   Part 3 is what lets the branch-width algorithm pick a base of a matroid attached to a leaf of a partial decomposition.
--
--   **Formalization Note** Part 1 is stated as $f^*(X, Y) \le f(Z)$ for every $Z$ with $X \subseteq Z$ and $Z \cap Y = \emptyset$, which is equivalent to the bound by the minimum. In part 3 "rank function of a matroid on $V \setminus B$" is the paper's rank axioms (i)–(iii) of p. 517 for subsets of $V \setminus B$.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 518, Proposition 4.1

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_Interpolation

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Proposition 4.1 (p. 518). -/
theorem interpolation_properties {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (hsub : IsSubmodular f) (hmin : ∀ X : Finset V, f ∅ ≤ f X)
    (fstar : Finset V → Finset V → ℤ) (hint : IsInterpolation f fstar) :
    (∀ X Y : Finset V, Disjoint X Y →
        ∀ Z : Finset V, X ⊆ Z → Disjoint Z Y → fstar X Y ≤ f Z) ∧
    (∀ Y : Finset V, fstar ∅ Y = f ∅) ∧
    ((∀ v : V, f {v} - f ∅ ≤ 1) →
        ∀ B : Finset V, IsMatroidRankOn Bᶜ (fun X => fstar X B - f ∅)) := by sorry

end ApproxCliqueWidth.Certificate
