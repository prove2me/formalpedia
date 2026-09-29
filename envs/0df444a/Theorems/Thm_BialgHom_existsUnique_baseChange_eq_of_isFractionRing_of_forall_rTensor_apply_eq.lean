-- Prove2me | Theorems.Thm_BialgHom_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
-- name    : BialgHom.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/e3205aa7-c05e-5735-b0d4-0cdef2b0321b
-- title:
--   Bialgebra descent along K ∩ ̂ O = O
-- statement:
--   Let $O$ be a commutative domain with fraction field $K$ (via an $O$-algebra structure making $K$ a fraction ring of $O$), let $\hat O$ be a commutative $O$-algebra, and let $\hat K$ be a commutative ring that is simultaneously an algebra over $O$, over $K$ and over $\hat O$, with the two scalar-tower compatibilities over $O$. Assume the structure map $\hat O \to \hat K$ is injective and the intersection condition: whenever $x \in K$ and $y \in \hat O$ have the same image in $\hat K$, then $x$ lies in the image of $O \to K$. Let $A$ and $B$ be commutative rings carrying $O$-bialgebra structures and finite free as $O$-modules. Let $g_K \colon K \otimes_O B \to K \otimes_O A$ be a $K$-bialgebra homomorphism and $g_{\hat O} \colon \hat O \otimes_O B \to \hat O \otimes_O A$ an $\hat O$-bialgebra homomorphism, and suppose that for every $b \in B$ the images of $g_K(1 \otimes b)$ and $g_{\hat O}(1 \otimes b)$ in $\hat K \otimes_O A$, under the maps induced on the left factor by $K \to \hat K$ and $\hat O \to \hat K$, coincide. Then there is a unique $O$-bialgebra homomorphism $g \colon B \to A$ whose base changes $\mathrm{id}_K \otimes g$ and $\mathrm{id}_{\hat O} \otimes g$ equal $g_K$ and $g_{\hat O}$ respectively.
--
--   This is the bialgebra form of the descent step $\operatorname{Hom}_O = \operatorname{Hom}_K \cap \operatorname{Hom}_{\hat O}$ used in Tate's theory of $p$-divisible groups: a homomorphism given over the fraction field and over a completion, agreeing in the larger ring, is already defined over $O$. It is obtained from the corresponding statement for $O$-linear maps of finite free modules, [`LinearMap.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq`](thm.html#LinearMap.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq), and is used in the construction of the family of bialgebra maps attached to a $p$-divisible group over a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_BialgHom_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u

open scoped TensorProduct

theorem BialgHom.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
    (O : Type u) [CommRing O] [IsDomain O] (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    (Oh : Type u) [CommRing Oh] [Algebra O Oh]
    (Kh : Type u) [CommRing Kh] [Algebra O Kh] [Algebra K Kh] [Algebra Oh Kh] [IsScalarTower O K Kh] [IsScalarTower O Oh Kh]
    (hinj : Function.Injective (algebraMap Oh Kh))
    (hcap : ∀ (x : K) (y : Oh), algebraMap K Kh x = algebraMap Oh Kh y → ∃ z : O, algebraMap O K z = x)
    (A : Type u) [CommRing A] [Bialgebra O A] [Module.Free O A] [Module.Finite O A]
    (B : Type u) [CommRing B] [Bialgebra O B] [Module.Free O B] [Module.Finite O B]
    (gK : K ⊗[O] B →ₐc[K] K ⊗[O] A) (gOh : Oh ⊗[O] B →ₐc[Oh] Oh ⊗[O] A)
    (hagree : ∀ b : B,
      ((IsScalarTower.toAlgHom O K Kh).toLinearMap.rTensor A) (gK ((1 : K) ⊗ₜ b)) =
        ((IsScalarTower.toAlgHom O Oh Kh).toLinearMap.rTensor A) (gOh ((1 : Oh) ⊗ₜ b))) :
    ∃! g : B →ₐc[O] A,
      Bialgebra.TensorProduct.map (BialgHom.id K K) g = gK ∧ Bialgebra.TensorProduct.map (BialgHom.id Oh Oh) g = gOh := by sorry
