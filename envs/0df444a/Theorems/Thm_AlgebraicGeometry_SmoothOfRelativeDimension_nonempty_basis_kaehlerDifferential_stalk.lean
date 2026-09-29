-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/8e792ab7-38d7-50ee-9b72-b9b587bd6832
-- title:
--   Free rank-n differentials at stalks of a smooth k-scheme
-- statement:
--   Let $k$ be a field (in a fixed universe), let $Y$ be a scheme, and let $p : Y \to \operatorname{Spec} k$ be a morphism of schemes which is smooth of relative dimension $n$ for a natural number $n$, in the sense of the Mathlib class `SmoothOfRelativeDimension n p`. Fix a point $y$ of $Y$. The stalk $\mathcal{O}_{Y,y} =$ `Y.presheaf.stalk y` is given the $k$-algebra structure coming from the ring map obtained by composing the inverse of the canonical isomorphism $k \xrightarrow{\sim} \Gamma(\operatorname{Spec} k, \top)$ with the map $p^{\sharp}$ on global sections `p.appTop` and then with the germ map $\Gamma(Y,\top) \to \mathcal{O}_{Y,y}$ at $y$; this algebra instance is introduced locally inside the statement so that the module of Kähler differentials $\Omega_{\mathcal{O}_{Y,y}/k}$ makes sense. The assertion is that the type of $\mathcal{O}_{Y,y}$-bases of $\Omega_{\mathcal{O}_{Y,y}/k}$ indexed by `Fin n` is nonempty; equivalently, $\Omega_{\mathcal{O}_{Y,y}/k}$ is a free $\mathcal{O}_{Y,y}$-module of rank exactly $n$. Note that the existence of a basis is asserted, not a chosen one.
--
--   This is the local, stalkwise form of the standard fact that a smooth morphism of relative dimension $n$ has locally free sheaf of relative differentials of rank $n$, here over a field base. It is used in the construction of the relative group law on Jacobians of good reduction, where it feeds into the affine-local formal unramifiedness statement [`GoodReductionJacobian.RelativeGroupLaw.exists_affine_formallyUnramified_stalkMap_action_one`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_affine_formallyUnramified_stalkMap_action_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk
    {k : Type u} [Field k] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p] (y : Y) :
    letI : Algebra k (Y.presheaf.stalk y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.toAlgebra
    Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄k])) := by sorry
