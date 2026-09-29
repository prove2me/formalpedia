-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma
-- name    : AlgebraicGeometry.Scheme.Modules.hom_ext_of_isIso_fromTildeGamma
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/b23e2102-80e3-55e3-8360-525d53b93ef2
-- title:
--   Maps out of Γ(M)̃xrightarrow∼M are determined on global sections
-- statement:
--   Let $R$ be a commutative ring, regarded as an object of `CommRingCat` in universe $u$, and let $M$ and $N$ be $\mathcal{O}$-modules on the scheme $\operatorname{Spec} R$, i.e. objects of `(Spec (.of R)).Modules`. Assume that the canonical morphism `Scheme.Modules.fromTildeΓ M`, the component at $M$ of the natural transformation `Scheme.Modules.fromTildeΓNatTrans` from the composite of the global-sections functor with the associated-module construction to the identity functor — that is, the map $\widetilde{\Gamma(\operatorname{Spec} R, M)} \to M$ — is an isomorphism. Let $\varphi, \psi \colon M \to N$ be two morphisms of $\mathcal{O}$-modules, and suppose that for every global section $m \in \Gamma(M,\top)$ one has $\varphi_\top(m) = \psi_\top(m)$, where $\varphi_\top$ and $\psi_\top$ denote the maps induced on sections over the whole space. Then $\varphi = \psi$ as morphisms of $\mathcal{O}$-modules. No hypothesis is imposed on $N$.
--
--   This is the usual faithfulness statement for the adjunction between global sections and the associated-module construction over an affine scheme: a morphism out of a module isomorphic to the module associated to its own global sections — for instance a quasi-coherent, in particular an invertible, module on $\operatorname{Spec} R$ — is determined by its effect on sections over the whole of $\operatorname{Spec} R$. It is used in the construction of isomorphisms of invertible modules on an affine chart from a prescribed linear isomorphism on sections, via [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.hom_ext_of_isIso_fromTildeGamma {R : CommRingCat.{u}}
    {M N : (Spec (.of R)).Modules} [IsIso (Scheme.Modules.fromTildeΓ M)] (φ ψ : M ⟶ N)
    (h : ∀ m : Γ(M, ⊤), φ.app ⊤ m = ψ.app ⊤ m) : φ = ψ := by sorry
