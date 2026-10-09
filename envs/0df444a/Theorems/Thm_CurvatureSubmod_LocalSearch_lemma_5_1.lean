-- Prove2me | Theorems.Thm_CurvatureSubmod_LocalSearch_lemma_5_1
-- name    : CurvatureSubmod.LocalSearch.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:24.406137+00:00
-- url     : https://prove2.me/theorems/a113025b-09d5-4c0d-b741-6cb4f4139330
-- title:
--   Lemma 5.1 (Brualdi), p. 6 — two bases $A, B$ admit a bijection $\pi : A \to B$ with $A - x + \pi(x)$ a base for all $x \in A$
-- statement:
--   Let $\mathcal M$ be a matroid on a finite ground set $X$, and let $A$ and $B$ be two bases of $\mathcal M$. Then there is a bijection $\pi : A \to B$ such that
--   $$A - x + \pi(x) \in \mathcal B(\mathcal M) \qquad \text{for all } x \in A.$$
--
--   This bijective exchange property, due to Brualdi (1969; see Schrijver, *Combinatorial Optimization*, Corollary 39.12a), indexes the single-element swaps between a local optimum and an optimal base that the local-search analysis compares.
--
--   **Formalization Note** The matroid is Mathlib's `Matroid X` with any ground set; $\pi$ is a function $X \to X$ that restricts to a bijection from $A$ onto $B$ (`Set.BijOn`). Mathlib has only the single-element exchange `Matroid.IsBase.exchange`.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 6, Lemma 5.1 (Brualdi [3])

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

namespace CurvatureSubmod.LocalSearch

/-- Lemma 5.1 (Brualdi), p. 6: two bases `A`, `B` of a matroid admit a bijection
`π : A → B` with `A − x + π(x)` a base for every `x ∈ A`. -/
theorem lemma_5_1 {X : Type} [Fintype X] [DecidableEq X] (M : Matroid X) (A B : Finset X)
    (hA : M.IsBase (↑A : Set X)) (hB : M.IsBase (↑B : Set X)) :
    ∃ π : X → X, Set.BijOn π (↑A : Set X) (↑B : Set X) ∧
      ∀ x ∈ A, M.IsBase (↑(insert (π x) (A.erase x)) : Set X) := by sorry

end CurvatureSubmod.LocalSearch
