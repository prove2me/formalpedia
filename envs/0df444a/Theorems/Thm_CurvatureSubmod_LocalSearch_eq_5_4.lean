-- Prove2me | Theorems.Thm_CurvatureSubmod_LocalSearch_eq_5_4
-- name    : CurvatureSubmod.LocalSearch.eq_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:51.469276+00:00
-- url     : https://prove2.me/theorems/792452b6-4aa7-406b-a576-c1f8b2422203
-- title:
--   Display (5.4), p. 7 (Filmus–Ward) — $\frac{e}{e-1} g(A) \ge g(B) + \sum_i [h(A) - h(A - a_i + b_i)]$
-- statement:
--   Let $X$ be a finite set, $g : 2^X \to \mathbb{R}_{\ge 0}$ monotone increasing and submodular, and $h$ the Filmus–Ward potential of $g$,
--   $$h(A) = \sum_{\emptyset \ne B \subseteq A} g(B) \int_0^1 \frac{e^p}{e-1}\, p^{|B|-1}(1-p)^{|A|-|B|}\, dp.$$
--   Let $A$ and $B$ be bases of a matroid $\mathcal M$ on $X$ and $\pi : A \to B$ a bijection with $A - a + \pi(a)$ a base for every $a \in A$ (as in Lemma 5.1); write $A = \{a_1, \dots, a_r\}$ and $b_i = \pi(a_i)$. Then
--   $$\frac{e}{e-1}\, g(A) \ \ge\ g(B) + \sum_{i=1}^r \bigl[h(A) - h(A - a_i + b_i)\bigr].$$
--
--   This is Filmus and Ward's inequality [17, Theorem 5.1]: the total gain available from the swaps $A - a_i + b_i$ in the potential $h$ controls how far $g(A)$ can fall below $(1 - e^{-1})\, g(B)$.
--
--   **Formalization Note** The page states (5.4) "for any submodular function $g$", citing [17], whose setting is monotone submodular $g$ normalised by $g(\emptyset) = 0$; the paper applies it only to the monotone nonnegative $g$ of Lemmas A.1 and A.2. The statement therefore assumes $g$ monotone increasing and nonnegative. The $B = \emptyset$ term of $h$ is excluded (see the Setting definition); with that convention the inequality holds for $g(\emptyset) \ge 0$, since the constant $g(\emptyset)$ adds the same amount to $h(A)$ and $h(A - a_i + b_i)$. The indexing $b_i = \pi(a_i)$ is a sum over $a \in A$.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), p. 7, display (5.4) in the proof of Lemma 5.2 (Filmus and Ward [17, Theorem 5.1, p. 526]); h defined on p. 7

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

namespace CurvatureSubmod.LocalSearch

/-- Display (5.4), p. 7 (Filmus–Ward [17, Theorem 5.1]):
`(e/(e − 1)) g(A) ≥ g(B) + Σ_i [h(A) − h(A − a_i + b_i)]` for bases indexed as in Lemma 5.1. -/
theorem eq_5_4 {X : Type} [Fintype X] [DecidableEq X] (g : Finset X → ℝ)
    (hg0 : ∀ A, 0 ≤ g A) (hgmono : MonoInc g) (hgsub : NonmonotoneSubmod.Shared.Submodular g)
    (M : Matroid X) (A B : Finset X)
    (hA : M.IsBase (↑A : Set X)) (hB : M.IsBase (↑B : Set X))
    (π : X → X) (hπ : Set.BijOn π (↑A : Set X) (↑B : Set X))
    (hswap : ∀ x ∈ A, M.IsBase (↑(insert (π x) (A.erase x)) : Set X)) :
    g B + ∑ a ∈ A, (hPot g A - hPot g (insert (π a) (A.erase a)))
      ≤ Real.exp 1 / (Real.exp 1 - 1) * g A := by sorry

end CurvatureSubmod.LocalSearch
