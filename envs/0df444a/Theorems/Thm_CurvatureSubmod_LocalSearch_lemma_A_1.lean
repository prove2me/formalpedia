-- Prove2me | Theorems.Thm_CurvatureSubmod_LocalSearch_lemma_A_1
-- name    : CurvatureSubmod.LocalSearch.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:55.280893+00:00
-- url     : https://prove2.me/theorems/813ea998-9536-4c89-bc61-f01804baa85b
-- title:
--   Lemma A.1, p. 14 — $g = f - \ell$ with $\ell(A)=\sum_{j\in A} f_{X-j}(j)$ is submodular, monotone increasing and nonnegative
-- statement:
--   Let $X$ be a finite set and $f : 2^X \to \mathbb{R}_{\ge 0}$ a monotone increasing submodular function. Define the linear function and the remainder
--   $$\ell(A) = \sum_{j \in A} f_{X-j}(j), \qquad g(A) = f(A) - \ell(A).$$
--   Then $g$ is submodular, monotone increasing, and nonnegative.
--
--   This is the decomposition $f = g + \ell$ on which the maximization algorithm of §6.1 runs: the local search is applied to the monotone submodular part $g$ and the linear part $\ell$ jointly.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 14, Lemma A.1

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

namespace CurvatureSubmod.LocalSearch

/-- Lemma A.1, p. 14: `g = f − ℓ` with `ℓ(A) = Σ_{j∈A} f_{X−j}(j)` is submodular, monotone
increasing and nonnegative. -/
theorem lemma_A_1 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hmono : MonoInc f) (hsub : NonmonotoneSubmod.Shared.Submodular f) :
    NonmonotoneSubmod.Shared.Submodular (gMax f) ∧ MonoInc (gMax f) ∧
      ∀ A, 0 ≤ gMax f A := by sorry

end CurvatureSubmod.LocalSearch
