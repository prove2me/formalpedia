-- Prove2me | Theorems.Thm_CartierDual_dualBaseChangeLin_bijective
-- name    : CartierDual.dualBaseChangeLin_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/ce2446a6-fb04-588c-a280-b02bf7ad43c1
-- title:
--   Cartier duality commutes with base change to a field
-- statement:
--   Let $O$ be a commutative ring, let $F$ be a field that is an $O$-algebra, and let $A$ be a commutative Hopf algebra over $O$ whose comultiplication is cocommutative and which is finite and free as an $O$-module. Write $A^\vee = \operatorname{Hom}_O(A,O)$ for [`CartierDual O A`](def/HopfAlgebra_CartierDual.html#L12), the $O$-dual of $A$ carrying its bialgebra structure (convolution product from the comultiplication of $A$, comultiplication transposed from the multiplication), and similarly $(F\otimes_O A)^\vee$ for the $F$-dual of the base change. Let $\beta =$ [`CartierDual.dualBaseChangeLin O F A`](def/HopfAlgebra_CharacterClosure.html#L151) be the $F$-linear map $F\otimes_O A^\vee \to (F\otimes_O A)^\vee$ obtained by base change from the $O$-linear comparison map `dualBaseChangeHom`, which sends a functional $\varphi$ on $A$ to the functional $c\otimes a\mapsto c\,\varphi(a)$ on $F\otimes_O A$. The assertion is a conjunction of five statements: $\beta$ is bijective; $\beta(1)=1$; $\beta(xy)=\beta(x)\beta(y)$ for all $x,y\in F\otimes_O A^\vee$; for every $g\in A^\vee$, applying $\beta\otimes\beta$ to the image of $\Delta_{A^\vee}(g)\in A^\vee\otimes_O A^\vee$ under [`tensorToGenericFibre`](def/FiniteFlat_ClosureHopf.html#L115) (the canonical map $M\otimes_O M\to (F\otimes_O M)\otimes_F(F\otimes_O M)$, $u\otimes v\mapsto (1\otimes u)\otimes(1\otimes v)$) yields $\Delta_{(F\otimes_O A)^\vee}(\beta(1\otimes g))$; and for every $g\in A^\vee$ and every $x\in F\otimes_O A$, $\beta(1\otimes S_{A^\vee}g)(x)=\beta(1\otimes g)(S_{F\otimes_O A}x)$, where $S$ denotes the relevant antipodes.
--
--   This is the statement that Cartier duality commutes with base change, in the case of a finite free commutative Hopf algebra and base change to a field, packaged so that the comparison map can be promoted to an isomorphism of $F$-algebras compatible with comultiplication and antipode. It feeds the analysis of characters and of the generic fibre of a finite flat commutative group scheme, in particular [`HopfAlgebra.characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable`](thm.html#HopfAlgebra.characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable) and [`HopfAlgebra.exists_characterClosure_points_equiv`](thm.html#HopfAlgebra.exists_characterClosure_points_equiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_dualBaseChangeLin_bijective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_HopfAlgebra_CharacterClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.dualBaseChangeLin_bijective.{u, v, w}
    (O : Type u) [CommRing O] (F : Type v) [Field F] [Algebra O F]
    (A : Type w) [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A] [Module.Finite O A] [Module.Free O A] :
    Function.Bijective (CartierDual.dualBaseChangeLin O F A) ∧
    CartierDual.dualBaseChangeLin O F A 1 = 1 ∧
    (∀ x y : F ⊗[O] CartierDual O A,
        CartierDual.dualBaseChangeLin O F A (x * y)
          = CartierDual.dualBaseChangeLin O F A x * CartierDual.dualBaseChangeLin O F A y) ∧
    (∀ g : CartierDual O A,
        TensorProduct.map (CartierDual.dualBaseChangeLin O F A) (CartierDual.dualBaseChangeLin O F A)
            (tensorToGenericFibre O F (Coalgebra.comul (R := O) g))
          = Coalgebra.comul (R := F) (CartierDual.dualBaseChangeLin O F A ((1 : F) ⊗ₜ[O] g))) ∧
    (∀ (g : CartierDual O A) (x : F ⊗[O] A),
        CartierDual.dualBaseChangeLin O F A ((1 : F) ⊗ₜ[O] HopfAlgebraStruct.antipode (R := O) g) x
          = CartierDual.dualBaseChangeLin O F A ((1 : F) ⊗ₜ[O] g) (HopfAlgebraStruct.antipode (R := F) x)) := by sorry
