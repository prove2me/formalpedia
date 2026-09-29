-- Prove2me | Theorems.Thm_Devaney_exists_subinterval_image_eq
-- name    : Devaney.exists_subinterval_image_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-17T14:20:52.230672+00:00
-- url     : https://prove2.me/theorems/db9066de-ee1e-475e-8e2e-1b2b66460c88
-- title:
--   A covering interval has a subinterval mapped exactly onto the target
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be continuous, and let $I$ and $J$ be closed bounded intervals, written here as $I=[a,b]$ and $J=[c,d]$ with endpoints given in either order. Suppose $I$ *covers* $J$, meaning $J\subseteq f(I)$. Then $I$ contains a closed subinterval that $f$ maps **exactly onto** $J$:
--
--   $$\exists\,K\subseteq I \text{ a closed interval such that } f(K)=J.$$
--
--   The point is that the covering hypothesis only gives the inclusion $J\subseteq f(I)$, so a priori $f(I)$ may be much larger than $J$; the conclusion produces a subinterval on which the image is neither too small nor too large. This is the tool that turns a chain of coverings into a genuine itinerary: applying it repeatedly backwards along a chain $I_0\to I_1\to\dots\to I_n$ yields nested subintervals whose iterates land in the prescribed intervals, which is what makes the loop construction for periodic points possible.
--
--   **Formalization Note** `Set.uIcc x y` is the closed interval with endpoints $x$ and $y$ in whichever order, so no ordering hypothesis on the endpoints is needed. `Covers f I J` abbreviates $J\subseteq f(I)$.
-- source:
--   V. L. Smirnov and J. J. Tolosa, The Sharkovsky Theorem, arXiv:1702.07964v1 (2017), https://arxiv.org/abs/1702.07964, Section 5, Lemma 3, page 9.

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem exists_subinterval_image_eq (f : ℝ → ℝ) (hf : Continuous f) (a b c d : ℝ)
    (h : Covers f (Set.uIcc a b) (Set.uIcc c d)) :
    ∃ u v : ℝ, Set.uIcc u v ⊆ Set.uIcc a b ∧ f '' Set.uIcc u v = Set.uIcc c d := by sorry
end Devaney
