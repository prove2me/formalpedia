-- Prove2me | Theorems.Thm_Algebra_exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit
-- name    : Algebra.exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/0b4382a2-53aa-56b5-8126-e89187c4d02a
-- title:
--   Kummer cover: roots of finitely many units
-- statement:
--   Let $R$ be a commutative ring, let $m$ be a natural number, and let $n : \mathrm{Fin}\,m \to \mathbb{N}$ be a family of exponents with $n_i > 0$ for each $i$ and such that the image of each $n_i$ under the canonical map $\mathbb{N} \to R$ is a unit of $R$. Let $u : \mathrm{Fin}\,m \to R^\times$ be a family of units of $R$. The assertion is the existence of a type $R'$ in the same universe as $R$, carrying a commutative ring structure and an $R$-algebra structure, such that $R'$ is finite as an $R$-module, faithfully flat as an $R$-module and étale as an $R$-algebra, together with a family of units $v : \mathrm{Fin}\,m \to R'^\times$ satisfying $v_i^{\,n_i} = u_i$ in $R'^\times$ for every $i$, where $u_i$ is transported to $R'^\times$ along the monoid homomorphism induced by $\mathrm{algebraMap}\, R\, R'$. Thus all the prescribed roots are extracted simultaneously in a single finite étale faithfully flat extension.
--
--   This is the standard Kummer-covering device: after a finite étale faithfully flat base change, finitely many given units acquire $n_i$-th roots, provided each $n_i$ is invertible. It is used in the construction of the extension over which a symmetric cocycle becomes a coboundary, via [`CommRing.exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card`](thm.html#CommRing.exists_etale_faithfullyFlat_units_eq_mul_inv_mul_inv_of_symm_of_cocycle_of_isUnit_card).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit
    (R : Type u) [CommRing R] {m : ℕ} (n : Fin m → ℕ) (hn : ∀ i, 0 < n i) (hnu : ∀ i, IsUnit ((n i : ℕ) : R))
    (u : Fin m → Rˣ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R') (_ : Module.FaithfullyFlat R R')
      (_ : Algebra.Etale R R') (v : Fin m → R'ˣ),
      ∀ i, (v i) ^ (n i) = Units.map (algebraMap R R' : R →* R') (u i) := by sorry
