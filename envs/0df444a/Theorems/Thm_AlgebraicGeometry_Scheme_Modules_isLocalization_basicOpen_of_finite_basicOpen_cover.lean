-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover
-- name    : AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_finite_basicOpen_cover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/250fb819-94ad-5de6-998d-5a5c04720698
-- title:
--   Localisation of module sections over a finite basic-open cover
-- statement:
--   Let $X$ be a scheme, $M$ a module over its structure sheaf (an object of `X.Modules`, so $\Gamma(M,V)$ is a $\Gamma(X,V)$-module functorially in the open $V$), let $U$ be an affine open of $X$, and let $s$ be a finite subset of $\Gamma(X,U)$ whose basic opens cover $U$, i.e. $U \le \bigsqcup_{h \in s} X_h$ where $X_h$ denotes `X.basicOpen h`. Call an open $V$ with a chosen ring of sections *localising* when for every $g \in \Gamma(X,V)$ the following two elementwise conditions hold: every $x \in \Gamma(M, X_g)$ satisfies $y|_{X_g} = (g^n)|_{X_g} \cdot x$ for some $n \in \mathbb{N}$ and some $y \in \Gamma(M,V)$; and every $y \in \Gamma(M,V)$ with $y|_{X_g} = 0$ satisfies $g^n \cdot y = 0$ for some $n \in \mathbb{N}$ (all restrictions being along the inclusion $X_g \le V$ given by `X.basicOpen_le`). Assume that each $X_h$ with $h \in s$ is localising, and that each intersection $X_h \sqcap X_{h'}$ with $h, h' \in s$ is localising. Then for every $f \in \Gamma(X,U)$ the two conditions hold with $V = U$ and $g = f$: every $x \in \Gamma(M, X_f)$ is of the form $y|_{X_f} = (f^n)|_{X_f} \cdot x$ for some $n$ and $y \in \Gamma(M,U)$, and every $y \in \Gamma(M,U)$ restricting to $0$ on $X_f$ is killed by a power of $f$.
--
--   This is the gluing half of the standard criterion that a sheaf of modules on an affine scheme whose sections over basic opens are localisations on the members and pairwise intersections of a finite standard open cover has the same property on the whole affine open; the two clauses express, elementwise, that $\Gamma(M, X_f)$ is the localisation of $\Gamma(M,U)$ at $f$. It is used by [`AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial`](thm.html#AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial), on the way to identifying sections of a quasi-coherent module over basic opens of an affine with localisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.lean

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_finite_basicOpen_cover
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens) (s : Finset Γ(X, U.1))
    (hs : U.1 ≤ ⨆ h ∈ s, X.basicOpen h)
    (hloc : ∀ h ∈ s, ∀ g : Γ(X, X.basicOpen h),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, X.basicOpen h)),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, X.basicOpen h), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, X.basicOpen h)) • y = 0)))
    (hloc₂ : ∀ h ∈ s, ∀ h' ∈ s, ∀ g : Γ(X, X.basicOpen h ⊓ X.basicOpen h'),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h'))),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h')), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, (X.basicOpen h ⊓ X.basicOpen h'))) • y = 0)))
    (f : Γ(X, U.1)) :
    ((∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, U.1)),
          M.presheaf.map (homOfLE (X.basicOpen_le f)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x)
        ∧ (∀ y : Γ(M, U.1), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
            ∃ n : ℕ, (f ^ n : Γ(X, U.1)) • y = 0)) := by sorry
