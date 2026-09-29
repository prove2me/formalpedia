-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul
-- name    : Deformation.DieudonneModule.map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/b3833bf5-7bb0-5a39-800d-0dfd7e799b05
-- title:
--   The Dieudonné module functor sends convolution to addition
-- statement:
--   Let $R$ be a commutative ring and $p$ a prime, and let $A$, $B$ be commutative $R$-bialgebras. Let $f$, $g$, $h \colon A \to B$ be bialgebra homomorphisms (`A →ₐc[R] B`), and assume that the $R$-linear map underlying $h$ factors as the comultiplication $\Delta_A \colon A \to A \otimes_R A$, followed by $f \otimes g$, followed by the multiplication map $B \otimes_R B \to B$; that is, $h = \mu_B \circ (f \otimes g) \circ \Delta_A$ as $R$-linear maps, so that $h$ is the convolution of $f$ and $g$. Here [`Deformation.DieudonneModule R p A`](def/Dieudonne_WittHomColimit.html#L234) is the direct limit, over $n$ with respect to the maps induced by the Witt shift, of the additive subgroups `wittHom R p n A` of `TruncatedWittVector p n A` consisting of those truncated Witt vectors $x$ whose image under the functorial action of `TruncatedWittVector p n` on the comultiplication ring homomorphism of $A$ equals the sum of its images under the two inclusions $A \to A \otimes_R A$; and [`Deformation.DieudonneModule.map R p φ`](def/Dieudonne_WittHomColimit.html#L380) is the additive homomorphism obtained by applying `TruncatedWittVector p n` levelwise to the algebra homomorphism underlying a bialgebra homomorphism $\varphi$. The conclusion is that for every $x$ in [`Deformation.DieudonneModule R p A`](def/Dieudonne_WittHomColimit.html#L234), $\;$ `map R p h x = map R p f x + map R p g x`.
--
--   This is the additivity of the Demazure–Gabriel Dieudonné module functor $\varinjlim_n \operatorname{Hom}(-, W_n)$ in the group law: convolution of bialgebra maps, i.e. addition of the corresponding maps of affine group schemes, is carried to addition in the Dieudonné module. It is used to exhibit the Dieudonné module as a module over endomorphism rings acting through bialgebra endomorphisms, and feeds into the bound on the rank of the Hecke-torsion part of a modular Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct in

theorem Deformation.DieudonneModule.map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul
    (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime]
    {A : Type} [CommRing A] [Bialgebra R A] {B : Type} [CommRing B] [Bialgebra R B]
    (f g h : A →ₐc[R] B)
    (hh : (h : A →ₐ[R] B).toLinearMap =
      LinearMap.mul' R B ∘ₗ TensorProduct.map (f : A →ₐ[R] B).toLinearMap (g : A →ₐ[R] B).toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := A))
    (x : Deformation.DieudonneModule R p A) :
    Deformation.DieudonneModule.map R p h x =
      Deformation.DieudonneModule.map R p f x + Deformation.DieudonneModule.map R p g x := by sorry
