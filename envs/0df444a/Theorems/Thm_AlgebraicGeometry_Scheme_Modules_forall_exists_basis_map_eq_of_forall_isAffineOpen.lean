-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen
-- name    : AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/a94e1d5a-32bc-5f61-a0b5-e13908d1a4a9
-- title:
--   Local bases on affine opens extend to all opens
-- statement:
--   Let $X$ be a scheme and let $M$ be an object of `X.Modules`, i.e. a sheaf of modules over the structure sheaf $\mathcal O_X$, with underlying presheaf `M.presheaf` and sheaf property `M.isSheaf`. Let $V$ be an open subset of $X$, let $d$ be a natural number, and let $e : \mathrm{Fin}\,d \to \Gamma(M, V)$ be a family of $d$ sections of $M$ over $V$. Assume that for every open $W$ with $W \le V$ such that $W$ is an affine open of $X$ there is a basis $b$ of the $\Gamma(X, W)$-module $\Gamma(M, W)$ indexed by $\mathrm{Fin}\,d$ with $b\,i$ equal to the restriction `M.presheaf.map (homOfLE hW).op (e i)` of $e\,i$ to $W$, for every $i$. The conclusion is the same assertion with the affineness requirement dropped: for every open $W$ with $W \le V$ there is a basis of $\Gamma(M, W)$ over $\Gamma(X, W)$, indexed by $\mathrm{Fin}\,d$, whose $i$-th member is the restriction of $e\,i$ to $W$. Thus the restricted family $e_1|_W, \dots, e_d|_W$ is a $\Gamma(X,W)$-basis of $\Gamma(M,W)$ for every open $W \subseteq V$.
--
--   This is the purely sheaf-theoretic step that upgrades a trivialisation of a sheaf of $\mathcal O_X$-modules recorded on affine opens only to one recorded on arbitrary opens; it lets freeness results proved chartwise by commutative algebra, where only affine charts are available, be used in the local-basis form required elsewhere. It is invoked in the treatment of relative Picard groups and of locally free modules of given rank, for instance for Kähler differentials and top differentials of a smooth morphism of given relative dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen
    {X : Scheme.{u}} (M : X.Modules) {V : X.Opens} {d : ℕ} (e : Fin d → Γ(M, V))
    (he : ∀ (W : X.Opens) (hW : W ≤ V), IsAffineOpen W →
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) := by sorry
