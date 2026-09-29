-- Prove2me | Theorems.Thm_Algebra_PointDerivations_exists_linearEquiv_tensor_forall_map_eq_of_finiteType
-- name    : Algebra.PointDerivations.exists_linearEquiv_tensor_forall_map_eq_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/b6760f29-fc05-56c9-8836-6c2a63e3864c
-- title:
--   Point derivations with values in M are P(k)⊗_k M
-- statement:
--   Let $k$ be a field and $A$ a commutative $k$-algebra of finite type, and let $\mathrm{ev} : A \to k$ be a ring homomorphism splitting the structure map, i.e. $\mathrm{ev}\circ(k\to A) = \mathrm{id}_k$. For a $k$-module $M$ (all types in the same universe as $k$ and $A$) write $\mathcal P(M) :=$ [`Algebra.PointDerivations k A ev M`](def/Algebra_PointDerivations.html#L9) for the $k$-submodule of $\mathrm{Hom}_k(A,M)$ consisting of those $k$-linear $D : A \to M$ satisfying $D(ab) = \mathrm{ev}(a)\cdot D(b) + \mathrm{ev}(b)\cdot D(a)$ for all $a,b \in A$, and for a $k$-linear map $g : M \to M'$ let [`Algebra.PointDerivations.map ev g`](def/Algebra_PointDerivations.html#L47) be the induced $k$-linear map $\mathcal P(M)\to\mathcal P(M')$, $D \mapsto g\circ D$. The assertion is the existence of a family $\Psi$ assigning to every $k$-module $M$ a $k$-linear isomorphism $\Psi_M : \mathcal P(M) \xrightarrow{\sim} \mathcal P(k)\otimes_k M$, such that (i) $\Psi$ is natural in $M$: for all $k$-modules $M, M'$, every $k$-linear $g : M \to M'$ and every $\delta \in \mathcal P(M)$ one has $\Psi_{M'}(g\circ\delta) = (\mathrm{id}_{\mathcal P(k)}\otimes g)(\Psi_M(\delta))$, and (ii) $\Psi$ is normalised at $M = k$: $\Psi_k(\delta) = \delta\otimes_k 1$ for every $\delta \in \mathcal P(k)$.
--
--   This is the statement that the Zariski tangent space at a rational point of a finite-type affine $k$-scheme has a finite-dimensional cotangent space, so that point derivations with coefficients in $M$ are obtained from those with coefficients in $k$ by base change, in a way compatible with maps of coefficient modules and normalised at $M = k$. It is used in the analysis of tangent vectors on the quaternionic Shimura curves entering the Čerednik–Drinfel'd setting, via [`CerednikDrinfeld.QM.exists_pointDerivations_linearEquiv_tensor_of_isTangentVector`](thm.html#CerednikDrinfeld.QM.exists_pointDerivations_linearEquiv_tensor_of_isTangentVector).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_PointDerivations_exists_linearEquiv_tensor_forall_map_eq_of_finiteType.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Scheme.TwoAffineOpenCover

universe u

theorem Algebra.PointDerivations.exists_linearEquiv_tensor_forall_map_eq_of_finiteType
    (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k) :
    ∃ Ψ : ∀ (M : Type u) [AddCommGroup M] [Module k M],
        ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (↥(Algebra.PointDerivations k A ev k) ⊗[k] M),
      (∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
          (δ : ↥(Algebra.PointDerivations k A ev M)),
        Ψ M' (Algebra.PointDerivations.map ev g δ) =
          LinearMap.lTensor (↥(Algebra.PointDerivations k A ev k)) g (Ψ M δ)) ∧
      (∀ δ : ↥(Algebra.PointDerivations k A ev k), Ψ k δ = δ ⊗ₜ[k] (1 : k)) := by sorry
