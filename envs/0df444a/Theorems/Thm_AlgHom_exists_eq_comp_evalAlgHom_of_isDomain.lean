-- Prove2me | Theorems.Thm_AlgHom_exists_eq_comp_evalAlgHom_of_isDomain
-- name    : AlgHom.exists_eq_comp_evalAlgHom_of_isDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/654a0680-4a64-5a8c-b00e-05756cb8f7ed
-- title:
--   Maps from a finite product to a domain factor through a projection
-- statement:
--   Let $K$ be a field and let $\Omega$ be a commutative $K$-algebra which is an integral domain. Let $J$ be a finite index type and let $(A_j)_{j \in J}$ be a family of commutative rings, each equipped with a $K$-algebra structure. The assertion is that for every $K$-algebra homomorphism $\varphi \colon \prod_{j \in J} A_j \to \Omega$ from the product algebra there exist an index $j \in J$ and a $K$-algebra homomorphism $\varphi_0 \colon A_j \to \Omega$ such that $\varphi$ equals the composite of the $j$-th coordinate projection `Pi.evalAlgHom K A j` followed by $\varphi_0$, i.e. $\varphi = \varphi_0 \circ \mathrm{pr}_j$. Only existence of the pair $(j, \varphi_0)$ is asserted; no uniqueness claim is made, and no finiteness, flatness or étaleness hypothesis is imposed on the factors $A_j$. Note that $J$ is allowed to be empty, in which case the product is the zero ring and, $\Omega$ being a domain and hence nonzero, no such $\varphi$ exists.
--
--   This is the algebraic form of the statement that $\operatorname{Spec}$ of a finite product of $K$-algebras is the disjoint union of the $\operatorname{Spec}$s of the factors, so that an $\Omega$-valued point lands in exactly one factor; equivalently $\operatorname{Hom}_K(\prod_j A_j, \Omega) = \coprod_j \operatorname{Hom}_K(A_j, \Omega)$ for $\Omega$ a domain. It is used when analysing $\Omega$-points of a finite product decomposition of an algebra, and is cited in the construction of model points on a generic fibre for finite flat inertia-stable data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_exists_eq_comp_evalAlgHom_of_isDomain.lean

import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgHom.exists_eq_comp_evalAlgHom_of_isDomain
    {K : Type*} [Field K] {Ω : Type*} [CommRing Ω] [Algebra K Ω] [IsDomain Ω]
    {J : Type*} [_root_.Finite J] {A : J → Type*} [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)]
    (φ : (Π j, A j) →ₐ[K] Ω) :
    ∃ (j : J) (φ₀ : A j →ₐ[K] Ω), φ = φ₀.comp (Pi.evalAlgHom K A j) := by sorry
