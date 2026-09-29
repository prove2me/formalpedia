-- Prove2me | Theorems.Thm_CartierDual_exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing
-- name    : CartierDual.exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/56b42f20-a580-52d1-a8b5-7ece463eaec6
-- title:
--   Reduction of the Cartier dual modulo 𝔪
-- statement:
--   Let $R$ be a commutative local ring with maximal ideal $\mathfrak m =$ `maximalIdeal R` and residue field $\kappa =$ `ResidueField R`, and let $B$ be a commutative ring carrying a Hopf algebra structure over $R$ which is finite and free as an $R$-module. Here [`CartierDual R B`](def/HopfAlgebra_CartierDual.html#L12) is by definition the $R$-module dual $\operatorname{Hom}_R(B,R)$, equipped with its ring (convolution) and $R$-algebra structure, and [`CartierDual.dualBaseChangeLin R κ B`](def/HopfAlgebra_CharacterClosure.html#L151) is the $\kappa$-linear map $\kappa \otimes_R \operatorname{Hom}_R(B,R) \to \operatorname{Hom}_\kappa(\kappa \otimes_R B, \kappa)$ obtained by base change from the $R$-linear map sending $\varphi$ to the functional determined by $c \otimes b \mapsto c\,\overline{\varphi(b)}$. The assertion is that there exists a ring homomorphism $r \colon \operatorname{Hom}_R(B,R) \to \operatorname{Hom}_\kappa(\kappa \otimes_R B,\kappa)$ between the two Cartier duals such that three conditions hold: $r(\varphi)$ equals `dualBaseChangeLin R κ B` applied to $1 \otimes_R \varphi$ for every $\varphi$; $r$ is surjective; and the kernel of $r$ is the ideal $\mathfrak m \cdot \operatorname{Hom}_R(B,R)$, namely the image ideal of $\mathfrak m$ under the structure map $R \to \operatorname{Hom}_R(B,R)$.
--
--   This is the statement that Cartier duality is compatible with passage to the special fibre of a local base, in the form of a presentation of the Cartier dual of the reduced Hopf algebra as the quotient of the Cartier dual by $\mathfrak m$. It is used to transfer idempotents of the Cartier dual of $\kappa \otimes_R B$ back to the Cartier dual of $B$ over a henselian local base, in the construction of group-algebra lifts of coalgebra maps ([`CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing`](thm.html#CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CharacterClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

theorem CartierDual.exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R]
    {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B] :
    ∃ r : CartierDual R B →+* CartierDual (ResidueField R) (ResidueField R ⊗[R] B),
      (∀ φ, r φ = CartierDual.dualBaseChangeLin R (ResidueField R) B ((1 : ResidueField R) ⊗ₜ[R] φ)) ∧
      Function.Surjective r ∧
      RingHom.ker r = (maximalIdeal R).map (algebraMap R (CartierDual R B)) := by sorry
