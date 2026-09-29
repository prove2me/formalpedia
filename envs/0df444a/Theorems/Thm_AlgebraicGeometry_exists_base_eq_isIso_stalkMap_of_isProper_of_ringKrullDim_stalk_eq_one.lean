-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one
-- name    : AlgebraicGeometry.exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/e29f304d-0c04-53f7-8acc-7e51d6637f27
-- title:
--   Proper birational morphisms are local isomorphisms at one-dimensional normal points
-- statement:
--   Let $k$ be a field and let $P'$, $P$ be schemes (in a fixed universe). Assume given a morphism $p : P \to \operatorname{Spec} k$ that is locally of finite type and quasi-compact, that both $P$ and $P'$ are integral, and that $\pi : P' \to P$ is proper. Assume further that there is an open subscheme $W$ of $P$ whose underlying set is non-empty such that the restricted morphism $\pi \mid_W : \pi^{-1}(W) \to W$ is an isomorphism; thus $\pi$ is birational. Finally let $w$ be a point of $P$ whose local ring $\mathcal{O}_{P,w}$ (the stalk of the structure presheaf at $w$) has Krull dimension equal to $1$, as an element of the extended natural numbers, and is integrally closed in its field of fractions. The conclusion is that there exists a point $w'$ of $P'$ such that $\pi$ sends $w'$ to $w$ on underlying topological spaces and the induced map of stalks $\mathcal{O}_{P,\pi(w')} \to \mathcal{O}_{P',w'}$ is an isomorphism of commutative rings.
--
--   This is the standard consequence of the valuative criterion of properness: a proper birational morphism onto an integral scheme of finite type over a field induces an isomorphism of local rings above any point whose local ring is a discrete valuation ring. It is used in the construction of the partial action in the good-reduction analysis of Jacobians, via [`GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one`](thm.html#GoodReductionJacobian.PartialAction.exists_closure_image_eq_closure_singleton_of_ringKrullDim_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one
    {k : Type u} [Field k] {P' P : Scheme.{u}} (p : P ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    [IsIntegral P] [IsIntegral P'] (π : P' ⟶ P) [IsProper π]
    (W : P.Opens) (hW : (W : Set P).Nonempty) [IsIso (π ∣_ W)]
    (w : P) (hw₁ : ringKrullDim (P.presheaf.stalk w) = 1) (hwn : IsIntegrallyClosed (P.presheaf.stalk w)) :
    ∃ w' : P', π.base w' = w ∧ IsIso (π.stalkMap w') := by sorry
