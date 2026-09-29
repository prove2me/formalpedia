-- Prove2me | Theorems.Thm_CoalgHom_exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
-- name    : CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/238dc9ba-0b12-5d3c-9314-2759d7629728
-- title:
--   Hensel lifting of coalgebra maps into R[M]
-- statement:
--   Let $R$ be a commutative ring which is a henselian local ring, with residue field $\kappa = \mathrm{ResidueField}\,R$, let $B$ be a commutative ring carrying a Hopf algebra structure over $R$ which is finite and free as an $R$-module and whose underlying coalgebra is cocommutative, and let $M$ be a finite additive abelian group. Suppose given a homomorphism of $\kappa$-coalgebras $f_0 \colon \kappa \otimes_R B \to \kappa[M]$, where $\kappa[M]$ is the additive monoid algebra of $M$ over $\kappa$. Then there exists a homomorphism of $R$-coalgebras $f \colon B \to R[M]$ whose reduction agrees with $f_0$ on the image of $B$: composing $f$ with the coefficient-change algebra map $R[M] \to \kappa[M]$ induced by $R \to \kappa$ gives the same $R$-linear map $B \to \kappa[M]$ as the map $b \mapsto 1 \otimes b$ from $B$ to $\kappa \otimes_R B$ followed by $f_0$ viewed as $R$-linear. Only existence is asserted; no uniqueness of $f$ is claimed.
--
--   This is the existence half of Hensel lifting for coalgebra maps into a group coalgebra: over a henselian local base, a coalgebra map from the special fibre of a finite free commutative Hopf algebra into $\kappa[M]$ comes from an $R$-coalgebra map into $R[M]$. It is used to obtain the corresponding lifting statement for bialgebra maps, [`HopfAlgebra.exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing`](thm.html#HopfAlgebra.exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CoalgHom_exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

theorem CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B] [Coalgebra.IsCocomm R B]
    (M : Type w) [AddCommGroup M] [Finite M]
    (f₀ : ResidueField R ⊗[R] B →ₗc[ResidueField R] AddMonoidAlgebra (ResidueField R) M) :
    ∃ f : B →ₗc[R] AddMonoidAlgebra R M,
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).toLinearMap ∘ₗ f.toLinearMap =
        (f₀.toLinearMap.restrictScalars R) ∘ₗ
          (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := B)).toLinearMap := by sorry
