-- Prove2me | Theorems.Thm_Algebra_card_algHom_le_finrank_residueField_tensorProduct
-- name    : Algebra.card_algHom_le_finrank_residueField_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/c37ed445-d413-57be-86a1-c066783df4c5
-- title:
--   Points of a finite algebra bounded by special-fibre dimension
-- statement:
--   Let $R$ be a commutative local ring, written $\kappa =$ `IsLocalRing.ResidueField R` for its residue field, let $B$ be a commutative $R$-algebra that is finite as an $R$-module, and let $\Omega$ be a field equipped with an $R$-algebra structure (no further compatibility between $\Omega$ and the local structure of $R$ is assumed: the map $R \to \Omega$ is an arbitrary ring homomorphism to a field). The assertion is the conjunction of two statements about the type $B \to_{\mathrm{alg}[R]} \Omega$ of $R$-algebra homomorphisms from $B$ to $\Omega$: first, that this type is finite; second, that its cardinality, measured by `Nat.card`, is at most $\dim_{\kappa}(\kappa \otimes_R B)$, the $\kappa$-dimension of the base change of $B$ to the residue field, i.e. of $B/\mathfrak{m}B$. Note that finiteness is delivered as a conjunct of the conclusion rather than as an instance hypothesis, and that the bound is stated for the `Nat.card` of the hom-type.
--
--   This is the bound on the number of $\Omega$-valued points of a finite $R$-scheme $\operatorname{Spec} B$ over a local base by the dimension (length) of its special fibre, obtained from Nakayama's lemma together with Dedekind's independence of characters. It is used by [`AlgebraicGeometry.finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite`](thm.html#AlgebraicGeometry.finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite), the geometric form of the same bound for finite morphisms of schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_card_algHom_le_finrank_residueField_tensorProduct.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.card_algHom_le_finrank_residueField_tensorProduct
    (R : Type*) [CommRing R] [IsLocalRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (Ω : Type*) [Field Ω] [Algebra R Ω] :
    Finite (B →ₐ[R] Ω) ∧
      Nat.card (B →ₐ[R] Ω) ≤
        Module.finrank (IsLocalRing.ResidueField R)
          (TensorProduct R (IsLocalRing.ResidueField R) B) := by sorry
