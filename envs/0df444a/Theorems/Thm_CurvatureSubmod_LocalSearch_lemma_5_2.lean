-- Prove2me | Theorems.Thm_CurvatureSubmod_LocalSearch_lemma_5_2
-- name    : CurvatureSubmod.LocalSearch.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:51.326579+00:00
-- url     : https://prove2.me/theorems/1c114847-a4ef-4962-bbba-34b6534cd98f
-- title:
--   Lemma 5.2, p. 7 — $g(A)+\ell(A) \ge (1-e^{-1})g(B)+\ell(B)+\sum_i[\psi(A)-\psi(A-a_i+b_i)]$
-- statement:
--   Let $X$ be a finite set, $g : 2^X \to \mathbb{R}_{\ge 0}$ monotone increasing and submodular, $\ell(A) = \sum_{j \in A} w(j)$ a linear function with arbitrary real weights $w$, $h$ the Filmus–Ward potential of $g$, and
--   $$\psi(A) = (1 - e^{-1})\, h(A) + \ell(A).$$
--   Let $A = \{a_1, \dots, a_r\}$ and $B = \{b_1, \dots, b_r\}$ be bases of a matroid $\mathcal M$ on $X$, indexed according to Lemma 5.1 so that $A - a_i + b_i$ is a base for all $1 \le i \le r$. Then
--   $$g(A) + \ell(A) \ \ge\ (1 - e^{-1})\, g(B) + \ell(B) + \sum_{i=1}^r \bigl[\psi(A) - \psi(A - a_i + b_i)\bigr].$$
--
--   If no swap improves $\psi$, the sum is nonpositive and $A$ is a joint $(1 - e^{-1}, 1)$-approximation for $g$ and $\ell$; this is the analysis of the non-oblivious local search of Figure 4.
--
--   **Formalization Note** The indexing is a bijection $\pi : A \to B$ (`Set.BijOn`) with $b_i = \pi(a_i)$; the sum runs over $a \in A$. As in (5.4), $g$ is assumed monotone and nonnegative, the setting in which the paper uses the lemma, and $h$ excludes the $B = \emptyset$ term.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 7, Lemma 5.2

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

namespace CurvatureSubmod.LocalSearch

/-- Lemma 5.2, p. 7: `g(A) + ℓ(A) ≥ (1 − e^{−1}) g(B) + ℓ(B) + Σ_i [ψ(A) − ψ(A − a_i + b_i)]`
for bases indexed as in Lemma 5.1. -/
theorem lemma_5_2 {X : Type} [Fintype X] [DecidableEq X] (g : Finset X → ℝ)
    (hg0 : ∀ A, 0 ≤ g A) (hgmono : MonoInc g) (hgsub : NonmonotoneSubmod.Shared.Submodular g)
    (w : X → ℝ) (M : Matroid X) (A B : Finset X)
    (hA : M.IsBase (↑A : Set X)) (hB : M.IsBase (↑B : Set X))
    (π : X → X) (hπ : Set.BijOn π (↑A : Set X) (↑B : Set X))
    (hswap : ∀ x ∈ A, M.IsBase (↑(insert (π x) (A.erase x)) : Set X)) :
    (1 - Real.exp (-1)) * g B + linFun w B
        + ∑ a ∈ A, (psi g w A - psi g w (insert (π a) (A.erase a)))
      ≤ g A + linFun w A := by sorry

end CurvatureSubmod.LocalSearch
