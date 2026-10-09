-- Prove2me | Theorems.Thm_CurvatureSubmod_LocalSearch_lemma_2_1
-- name    : CurvatureSubmod.LocalSearch.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:05.579634+00:00
-- url     : https://prove2.me/theorems/bfa40872-7f84-4ca3-be92-4b5c32a694b6
-- title:
--   Lemma 2.1, p. 4 — $\sum_{j\in A} f_{X-j}(j) \ge (1-c) f(A)$ for monotone submodular $f$ of curvature $\le c$ with $f(\emptyset)=0$
-- statement:
--   Let $X$ be a finite set and $f : 2^X \to \mathbb{R}_{\ge 0}$ a monotone increasing submodular function with $f(\emptyset) = 0$ and total curvature at most $c$, i.e. $f_{X-j}(j) \ge (1-c) f_\emptyset(j)$ for every $j \in X$. Then for every $A \subseteq X$,
--   $$\sum_{j \in A} f_{X-j}(j) \ \ge\ (1-c)\, f(A).$$
--
--   The left-hand side is the linear function $\ell$ of §6.1; the lemma says that this linear part already captures a $(1-c)$ fraction of $f$, which is where the curvature enters the $1 - c/e$ guarantee of Theorem 6.1.
--
--   **Formalization Note** The hypothesis $f(\emptyset) = 0$ is added: the printed lemma is false without it. For $f(A) = 1 + |A|$ (monotone, submodular, nonnegative, curvature $0$) the left side is $|A| < 1 + |A|$; the proof's last step $(1-c)[f(A) - f(\emptyset)] \ge (1-c) f(A)$ goes the wrong way. No range of $c$ is assumed: for $c > 1$ the right side is nonpositive and the statement still holds. Curvature is in product form (see the Setting definition).
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 4, Lemma 2.1 (proof p. 14)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

namespace CurvatureSubmod.LocalSearch

/-- Lemma 2.1, p. 4 (proof p. 14), with the added hypothesis `f ∅ = 0`. -/
theorem lemma_2_1 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hmono : MonoInc f) (hsub : NonmonotoneSubmod.Shared.Submodular f)
    (c : ℝ) (hcurv : CurvAtMostInc f c) (hempty : f ∅ = 0) (A : Finset X) :
    (1 - c) * f A ≤ ∑ j ∈ A, marg f (Finset.univ.erase j) j := by sorry

end CurvatureSubmod.LocalSearch
