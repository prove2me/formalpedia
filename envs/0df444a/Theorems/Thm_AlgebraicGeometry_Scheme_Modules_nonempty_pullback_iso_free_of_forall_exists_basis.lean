-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_free_of_forall_exists_basis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/257465e4-4e7b-53f6-9ed4-d3c4e2ff928f
-- title:
--   Global basis on all opens below U makes M|_U free
-- statement:
--   Let $X$ be a scheme, $n$ a natural number, $M$ a sheaf of $\mathcal O_X$-modules on $X$, $U$ an open of $X$, and $e : \mathrm{Fin}\,n \to \Gamma(M, U)$ a finite family of sections of $M$ over $U$. Assume that for every open $W$ of $X$ with $W \le U$ there exists a basis of the $\Gamma(X, W)$-module $\Gamma(M, W)$ indexed by $\mathrm{Fin}\,n$ whose $i$-th member is the image of $e\,i$ under the restriction map $\Gamma(M, U) \to \Gamma(M, W)$ induced by the inclusion $W \le U$; that is, the restrictions of $e_0, \dots, e_{n-1}$ form a $\Gamma(X, W)$-basis of $\Gamma(M, W)$ for every such $W$. The conclusion asserts that the type of isomorphisms, in the category of sheaves of modules on the open subscheme $U$, between the inverse image of $M$ along the canonical open immersion $U.\iota$ and the free sheaf of modules on the index type $\mathrm{ULift}(\mathrm{Fin}\,n)$ is nonempty; so $M|_U \cong \mathcal O_U^{\,n}$, with the isomorphism asserted to exist rather than exhibited.
--
--   This is the sufficiency half of the description of a free module sheaf by a global frame: a family of $n$ sections that is a basis on every open contained in $U$ trivialises $M$ over $U$. It is used to establish that the sheaf of Kähler differentials and its top exterior power of a smooth morphism of given relative dimension are locally free of the expected rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_free_of_forall_exists_basis
    {X : Scheme.{u}} {n : ℕ} (M : X.Modules) (U : X.Opens) (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) := by sorry
