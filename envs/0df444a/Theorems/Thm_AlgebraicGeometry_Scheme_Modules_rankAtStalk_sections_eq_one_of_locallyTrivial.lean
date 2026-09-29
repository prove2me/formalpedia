-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial
-- name    : AlgebraicGeometry.Scheme.Modules.rankAtStalk_sections_eq_one_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/e5942112-b5fb-523d-acfe-370607bacaa3
-- title:
--   Sections of a locally trivial module have rank one on affine opens
-- statement:
--   Let $X$ be a scheme and let $M$ be an object of `X.Modules`, i.e. a sheaf of modules over the sheaf of rings $\mathcal{O}_X$. Assume $M$ is locally trivial in the following sense: for every point $x$ of $X$ there is an open subset $V \subseteq X$ with $x \in V$ such that the pullback of $M$ along the inclusion morphism $V.\iota : V \to X$ is isomorphic, as a sheaf of modules on $V$, to the unit object `SheafOfModules.unit` of the sheaf of rings of $V$ — that is, to $\mathcal{O}_V$ itself (the hypothesis asserts that the type of such isomorphisms is nonempty, not a chosen isomorphism). Let $U$ be an affine open of $X$, so that $\Gamma(M, U)$ is a module over the ring $\Gamma(X, U)$, and let $\mathfrak{p}$ be a prime ideal of $\Gamma(X, U)$. The conclusion is that the rank at the stalk $\mathfrak{p}$ of the $\Gamma(X, U)$-module $\Gamma(M, U)$, namely the rank of the localised module $\Gamma(M, U)_{\mathfrak{p}}$ over $\Gamma(X, U)_{\mathfrak{p}}$, equals $1$.
--
--   This is the affine-local rank computation for an invertible sheaf: on an affine open, the module of sections of a Zariski-locally trivial sheaf of modules has rank one at every prime. Together with the finiteness statement [`AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial`](thm.html#AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial) and the localisation statement [`AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial`](thm.html#AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial), it exhibits $\Gamma(M, U)$ as a finitely generated projective module of rank one, and it is used to compute the rank of sections after base change in [`AlgebraicGeometry.Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial`](thm.html#AlgebraicGeometry.Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_sections_eq_one_of_locallyTrivial
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (𝔭 : PrimeSpectrum Γ(X, U.1)) :
    Module.rankAtStalk (R := Γ(X, U.1)) Γ(M, U.1) 𝔭 = 1 := by sorry
