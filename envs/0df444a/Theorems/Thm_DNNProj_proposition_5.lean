-- Prove2me | Theorems.Thm_DNNProj_proposition_5
-- name    : DNNProj.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:39.250183+00:00
-- url     : https://prove2.me/theorems/6ae62e75-810d-40ca-a19e-daebcf6e8717
-- title:
--   Proposition 5 — a sufficient condition for bounded linear regularity
-- statement:
--   Let $D_1,\dots,D_m\subseteq\mathbb X$ be closed convex sets for some positive integer $m$, and let $D_1,\dots,D_r$ be polyhedral for some $r\in\{0,1,\dots,m\}$. If
--   $$\bigcap_{i=1}^{r}D_i\ \cap\ \bigcap_{i=r+1}^{m}\operatorname{ri}(D_i)\ne\emptyset,$$
--   then $\{D_1,\dots,D_m\}$ is boundedly linearly regular (Definition 3). Here $\operatorname{ri}$ is the relative interior.
--
--   **Formalization Note** Sets are indexed by `Fin m` (0-based), so the polyhedral ones are those with index $<r$; $\operatorname{ri}$ is `intrinsicInterior ℝ`.
--
--   Differences from the source:
--   - encoding: finite-dimensional real Euclidean spaces 𝕏, 𝕎, 𝕐 → real inner-product spaces with [FiniteDimensional ℝ _]; reason: Lean convention; same spaces
--   - encoding: polyhedral convex set → finite intersection of half-spaces {z | φᵢ z ≤ βᵢ} with φᵢ linear functionals (IsPolyhedral); reason: the standard definition; the empty set and the whole space are included
--   - encoding: indices 1, …, m with D₁, …, D_r polyhedral → Fin m (0-based), polyhedral for i.val < r; reason: Lean convention; same sets
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, Proposition 5, p.8

import Mathlib
import Definitions.Def_DNNProj_Basics

open scoped RealInnerProductSpace

namespace DNNProj

/-- **Proposition 5** (Cui–Liang–Sun–Toh, arXiv:2009.11272v2, p.8; [5, Corollary 3]). Let
`D₁, …, D_m ⊆ 𝕏` be closed convex sets for some positive integer `m`, and let `D₁, …, D_r` be
polyhedral for some `r ∈ {0, 1, …, m}`. Then a sufficient condition for `{D₁, …, D_m}` to be
boundedly linearly regular is
`⋂_{i=1,…,r} Dᵢ ∩ ⋂_{i=r+1,…,m} ri(Dᵢ) ≠ ∅`.

**Formalization Note.** The sets are indexed by `Fin m` (0-based), so "`i ≤ r`" is
`i.val < r`. `ri` is `intrinsicInterior ℝ` (the interior relative to the affine hull). `𝕏` is a
finite-dimensional real inner-product space. `r = 0` and `r = m` are both allowed. -/
theorem proposition_5 {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {m : ℕ} (hm : 0 < m) (D : Fin m → Set X) (hD : ∀ i, IsClosed (D i) ∧ Convex ℝ (D i))
    (r : ℕ) (hr : r ≤ m) (hpoly : ∀ i : Fin m, i.val < r → IsPolyhedral (D i))
    (hcq : ∃ x : X, ∀ i : Fin m,
      (i.val < r → x ∈ D i) ∧ (r ≤ i.val → x ∈ intrinsicInterior ℝ (D i))) :
    BoundedLinRegular D := by sorry

end DNNProj
