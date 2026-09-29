-- Prove2me | Theorems.Thm_CommRing_exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card
-- name    : CommRing.exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/d2e7a026-a940-5ddb-ae8e-82169befb3b7
-- title:
--   Symmetric 2-cocycles of units split over an étale cover
-- statement:
--   Let $R$ be a commutative ring and let $K$ be a finite additive abelian group whose order $|K|$, viewed in $R$ via the canonical map $\mathbb{N} \to R$, is a unit. Let $c : K \times K \to R^{\times}$ be a function with values in the units of $R$ which is symmetric, $c(a,b) = c(b,a)$ for all $a, b \in K$, and satisfies the cocycle identity $c(a,b)\,c(a+b,k) = c(b,k)\,c(a,b+k)$ for all $a, b, k \in K$. The assertion is that there exists a type $R'$ carrying a commutative ring structure and an $R$-algebra structure such that $R'$ is faithfully flat as an $R$-module and étale as an $R$-algebra, together with a function $b : K \to R'^{\times}$ such that for all $k, k' \in K$ the image of $c(k,k')$ under the induced map of unit groups $R^{\times} \to R'^{\times}$ equals $b(k+k')\,b(k)^{-1}\,b(k')^{-1}$. Thus $c$ becomes a coboundary after base change to $R'$. The conclusion asserts faithful flatness and étaleness only; module-finiteness of $R'$ over $R$ is not part of the statement.
--
--   This is the splitting of a symmetric unit-valued $2$-cocycle of a finite abelian group of invertible order after passage to a finite étale faithfully flat cover, i.e. the Kummer-theoretic trivialisation of the obstruction class. It is used in the construction of level structures on polarised abelian schemes after an étale faithfully flat base change, via [`AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_etale_levelLift_of_forall_act_comm`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_etale_levelLift_of_forall_act_comm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CommRing_exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CommRing.exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card
    (R : Type) [CommRing R] {K : Type} [AddCommGroup K] [Fintype K]
    (hK : IsUnit ((Fintype.card K : ℕ) : R))
    (c : K → K → Rˣ) (hsymm : ∀ a b : K, c a b = c b a)
    (hcocycle : ∀ a b k : K, c a b * c (a + b) k = c b k * c a (b + k)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R'), Module.FaithfullyFlat R R' ∧ Algebra.Etale R R' ∧
      ∃ b : K → R'ˣ, ∀ k k' : K,
        Units.map (algebraMap R R').toMonoidHom (c k k') = b (k + k') * (b k)⁻¹ * (b k')⁻¹ := by sorry
